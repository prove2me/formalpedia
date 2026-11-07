-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_4_5
-- name    : GeoSemialgCSP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:35.07279+00:00
-- url     : https://prove2.me/theorems/316c299e-afb5-44dd-9d08-b1bd5c9610c5
-- title:
--   Lemma 4.5 — moving noise to the solution
-- statement:
--   Assume the standing hypotheses of Section 4 (as in Lemma 4.4), and let $0<\eta<1$, $\rho=1-\eta$. For every fractional solution $\xi$ — points $x_1,\dots,x_n\in X$ and a map $\xi:[M]^R\to\mathcal P_n$ —
--   $$\mathrm{val}(\xi,(D_R)_P)=\mathrm{val}(T_\rho\xi,(J_R)_P).\tag{3}$$
--
--   The noise of the test can be moved onto the solution; this is how soundness reduces to the smoothed solution $T_\rho\xi$.
--
--   Differences from the source:
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - generalization: property (2): a cousins homomorphism for every finite ordered k-ary tree → HasCousinsHoms: one for every complete ordered k-ary tree; reason: a weaker hypothesis: every finite ordered k-ary tree embeds in a complete one preserving cousins tuples, so the printed property implies it; the proof uses only complete trees (Lemma 4.3 item 4)
--   - encoding: a fractional solution ξ : [M]^R → finitely supported distributions on X → points x : Fin n → E d in X and G : [M]^R → P_n; reason: the paper's own description (p.12): all distributions live on one finite set {x₁, …, x_n}
--   - generalization: R ≥ 1 (Let R ≥ 1, p.11) → every R : ℕ; reason: the R ≥ 1 cases are included; at R = 0 the test has a single variable and the inequality also holds
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.5, Eq. (3), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_HasCousinsHoms
import Definitions.Def_GeoSemialgCSP_MSSound
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3
import Definitions.Def_GeoSemialgCSP_valD
import Definitions.Def_GeoSemialgCSP_valJ
import Definitions.Def_GeoSemialgCSP_fS
import Definitions.Def_GeoSemialgCSP_noiseOpV

namespace GeoSemialgCSP

/-- **Lemma 4.5 (moving noise to the solution).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.5, Eq. (3), printed p.13 (PDF
p.14): for every fractional solution `ξ`, `val(ξ, (D_R)_P) = val(T_ρξ, (J_R)_P)`, `ρ = 1 − η`.

**Formalization Note.** A fractional solution is `(n, x, G)`: points `x₁, …, x_n ∈ X` and
`G : [M]^R → P_n`; its value is the multilinear extension of `a ↦ P(x_{a₁}, …, x_{a_k})`. The
standing assumptions of §4 are hypotheses, as in Lemma 4.4. -/
theorem lemma_4_5 {k d : ℕ} (hk : 2 ≤ k) (X : Set (E d)) (S : Set (Fin k → E d))
    (hsa : IsSemialgebraicPred S) (hcous : HasCousinsHoms X S)
    (q₀ : ℕ) (ε : ℝ) (hq₀ : 1 ≤ q₀) (hε : 0 < ε) {h H : ℕ} (hh : 1 ≤ h) (hms : MSSound k q₀ ε h)
    (L : PMF ((Fin h → Fin k) → Wd k H)) (εL : ℝ) (hεL : 0 < εL)
    (hL1 : RE1 L) (hL2 : RE2 L) (hL3 : RE3 L εL)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (R n : ℕ) (x : Fin n → E d) (hx : ∀ i, x i ∈ X)
    (G : (Fin R → Wd k H) → Fin n → ℝ) (hG : ∀ z, G z ∈ stdSimplex ℝ (Fin n)) :
    valD L R η (fS S x) G = valJ L R (fS S x) (noiseOpV (1 - η) G) := by sorry

end GeoSemialgCSP
