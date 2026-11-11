-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_3_7
-- name    : HZFixp.Main.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:24.522328+00:00
-- url     : https://prove2.me/theorems/8da49f97-fd29-4907-b35a-9a3393458f7f
-- title:
--   Lemma 3.7 — sign relation between a gate's output contribution and its arithmetic error
-- statement:
--   Consider a harmonic, reciprocal or feedback gate with output node value $x$, private node value $y$ and inputs $A$, all in their declared intervals: for a harmonic gate $0<a_1<b_1<a_2<b_2$, $\rho\in(0,1)$, $A\in[a_1,b_1]$, $B\in[a_2,b_2]$, $x$ in a positive output interval containing $[H_\rho(a_1,a_2),H_\rho(b_1,b_2)]$, $y\in[0.999,1.001]$; for a reciprocal gate $\kappa>0$, $c\ge0$, $A\in[a,b]$ with $a>0$, $x\in[\ell,u]\subset(0,\infty)$ with $[J(b),J(a)]\subseteq[\ell,u]$, an integer center $T\ge\max\{1,20(u+|\beta|)\}$, $y\in[0.999T,1.001T]$; for a feedback gate $\beta\ge2$, $T=2\beta$, a positive input $Y$, $x=z_j\in[1,2]$, $y\in[0.999T,1.001T]$. If the private node satisfies its box condition (3) with field $G_y$ of (9), then
--   $$\operatorname{sgn} h = -\operatorname{sgn}\big(x - x^\star(A)\big),\qquad h = 0 \iff y = T \iff x = x^\star(A). \tag{12}$$
--   Here $h$ and $G_y$ carry a common positive factor $\mu$, the gate's edge-multiplicity scaling.
--
--   The lemma converts each gate's arithmetic error into the sign of its contribution at the output node; it drives the error analysis that forces every gate in the reciprocal graph to evaluate exactly.
--
--   Differences from the source:
--   - generalization: the gate as constructed (Table 2, Figures 5–6; feedback multiplicities scaled by C^fb_j) → h and G_y multiplied by an arbitrary common factor μ > 0; reason: μ = 1 is the harmonic and reciprocal gate, μ = C^fb_j the feedback gate after clearing denominators, and μ = M_g a gate after the gadget scaling of B.1.4; the statement is unchanged by a positive factor
--   - generalization: rational gate parameters → real parameters; reason: the statement is pointwise real analysis; rational parameters are a special case
--   - reading: x⋆ for the three gate types → x⋆ = 1/Q(T, A) − T with the gate's own Q (so x⋆ = H_ρ(A, B), J(A), Y + 1 − β by Lemma B.1, B.2 and the feedback formula); reason: the definition of x⋆ in the basic-gate framework, p. 15
--   - reading: declared input interval of the feedback gate → any positive Y; reason: Y_j is the output of an affine gadget with a positive declared interval; every such interval is covered
--   - reading: harmonic gate on inputs A ∈ [a_1, b_1], B ∈ [a_2, b_2] (§3.3.2, Figure 5) → 0 < a_1 < b_1 < a_2 < b_2 and 0 < ρ < 1; reason: the separated input intervals b_1 < a_2 are what B.1.2 verifies ("the separated intervals"; every harmonic gate of §3.3.1 has them), node intervals lie in (0, ∞) (p. 6), and ρ, 1 − ρ are edge multiplicities, hence positive
--   - reading: reciprocal gate J(A) = κ/(A + c) + β (§3.3.2, Figure 6) → κ > 0 and c ≥ 0; reason: κ/R_T² and κ/(R_T D_T) are edge multiplicities and D_T/R_T an edge ratio, so κ > 0 and D_T = κ + R_T c > 0 for every admissible center T, which for arbitrarily large T (11) means c ≥ 0; every reciprocal gate of §3.3.1 has c ∈ {0, 1}
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 19 (PDF 21), Lemma 3.7, (12); proof B.1.1, pp. 48–49 (PDF 50–51)

import Mathlib
import Definitions.Def_HZFixp_Main_ReciprocalVI
import Definitions.Def_HZFixp_Main_Gates

namespace HZFixp.Main

/-- **Lemma 3.7.** For every harmonic, reciprocal, or feedback gate, the private-node box condition
implies `sgn h = −sgn(x − x⋆(A))` and `h = 0 ⇔ y = T ⇔ x = x⋆(A)` (12). Each gate's edges carry a
common positive multiplicity factor `μ`, which multiplies both `h` and the private field `G_y`. -/
theorem lemma_3_7 :
    (∀ (μ ρ a₁ b₁ a₂ b₂ ℓ u A B x y : ℝ), 0 < μ → 0 < ρ → ρ < 1 → 0 < a₁ → a₁ < b₁ → b₁ < a₂ →
      a₂ < b₂ → 0 < ℓ → ℓ ≤ harmH ρ a₁ a₂ → harmH ρ b₁ b₂ ≤ u →
      A ∈ Set.Icc a₁ b₁ → B ∈ Set.Icc a₂ b₂ → x ∈ Set.Icc ℓ u →
      BoxCond 0.999 1.001 y (μ * gateGy (-1) x y (harmQ ρ y A B)) →
      SignType.sign (μ * gateH (-1) x y 1) =
          -SignType.sign (x - gateXStar (harmQ ρ 1 A B) 1) ∧
        (μ * gateH (-1) x y 1 = 0 ↔ y = 1) ∧ (y = 1 ↔ x = gateXStar (harmQ ρ 1 A B) 1)) ∧
    (∀ (μ κ c β a b ℓ u : ℝ) (T : ℕ) (A x y : ℝ), 0 < μ → 0 < κ → 0 ≤ c → 0 < a → a ≤ b →
      0 < ℓ → ℓ ≤ recJ κ c β b → recJ κ c β a ≤ u → 1 ≤ T → 20 * (u + |β|) ≤ (T : ℝ) →
      A ∈ Set.Icc a b → x ∈ Set.Icc ℓ u →
      BoxCond (0.999 * T) (1.001 * T) y (μ * gateGy 1 x y (recQ κ c β T y A)) →
      SignType.sign (μ * gateH 1 x y T) =
          -SignType.sign (x - gateXStar (recQ κ c β T T A) T) ∧
        (μ * gateH 1 x y T = 0 ↔ y = T) ∧ (y = T ↔ x = gateXStar (recQ κ c β T T A) T)) ∧
    (∀ (μ β Y x y : ℝ), 0 < μ → 2 ≤ β → 0 < Y → x ∈ Set.Icc (1 : ℝ) 2 →
      BoxCond (0.999 * (2 * β)) (1.001 * (2 * β)) y (μ * gateGy 1 x y (fbQ β y Y)) →
      SignType.sign (μ * gateH 1 x y (2 * β)) =
          -SignType.sign (x - gateXStar (fbQ β (2 * β) Y) (2 * β)) ∧
        (μ * gateH 1 x y (2 * β) = 0 ↔ y = 2 * β) ∧
        (y = 2 * β ↔ x = gateXStar (fbQ β (2 * β) Y) (2 * β))) := by sorry

end HZFixp.Main
