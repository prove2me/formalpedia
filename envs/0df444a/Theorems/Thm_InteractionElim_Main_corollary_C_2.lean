-- Prove2me | Theorems.Thm_InteractionElim_Main_corollary_C_2
-- name    : InteractionElim.Main.corollary_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:24:18.44827+00:00
-- url     : https://prove2.me/theorems/7eed6991-18ab-4f3d-ae5a-2d0648ba4ea9
-- title:
--   Corollary C.2 — machine-only finite-call stage procedure with risk $\le\delta/m$ and expected fee $\le Cw\{t_0L+r\ln(r+1)+rL/R^3\}$
-- statement:
--   Let $D\subseteq\{0,1\}^r$ with $r\le R$, $R\ge16$, and suppose every $z\in D$ has a certificate (against $D$) of total mass at most $t_0$. Let $m$ be the number of stages ($1\le m\le R$), the desired stage risk $\sigma=\delta/m$, and assume $L=\ln(1/\delta)\ge\ln(R+1)$, $\delta\in(0,1)$. Coordinates have independent BSC responses with parameters $p_i\in[1/8,3/8]$ and each call costs $w>0$. There is a universal constant $C$ such that, for non-singleton $D$, there is a machine-only, finite-call procedure with risk at most $\sigma$ at each truth and expected fee at most
--   $$
--   Cw\{t_0L+r\ln(r+1)+rL/R^3\}. \tag{C.12}
--   $$
--   A singleton is submitted exactly.
--
--   Formally: if $|D|\ge2$ there is a measurable agent-only procedure on the coordinate menu, with a deterministic cap on its calls, such that at every truth $x\in D$ the probability of not submitting $x$ is at most $\delta/m$ and $w\cdot\mathbb E_x[\text{calls}]$ is at most (C.12); if $|D|=1$ there is a procedure that submits the element of $D$ with no call.
--
--   This is the execution step of the initial-teaching upper bound at each stage.
--
--   Differences from the source:
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - generalization: rational p_i, δ, w (§2: 'known rational p_i', 'rational w', 'Let δ ∈ (0,1) be rational') → real p_i ∈ [1/8, 3/8], δ ∈ (0,1), w > 0; reason: the corollary's own statement does not use rationality; rational values are a special case
--   - reading: 'a machine-only, finite-call procedure' → a measurable agent-only `Procedure` on the coordinate menu with a natural-number cap on its calls valid at every truth in D and every outcome; reason: machine-only = no expert; finite-call = deterministic call cap (§C.2 proof: 'Each component has a deterministic finite call cap')
--   - reading: m, the stage count in σ = δ/m → any m with 1 ≤ m ≤ R; reason: m is the number of nonempty blocks of [R]
--   - encoding: 'every z ∈ D has a certificate of total mass at most t0' → for every z ∈ D a feasible certificate a against D with ∑ a_i ≤ t0; reason: literal
--   - reading: 'risk at most σ at each truth' and 'expected fee' → for each truth x ∈ D, the probability of not outputting x is ≤ δ/m, and w times the expected number of calls is ≤ (C.12); reason: the procedure's failure is a wrong or missing submission; its fee is its calls
--   - reading: 'A singleton is submitted exactly.' → if |D| = 1, a procedure that outputs the element of D on every outcome with zero calls; reason: literal
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 36, Corollary C.2, Eq. (C.12)

import Mathlib
import Definitions.Def_InteractionElim_Main_Procedure

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem corollary_C_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R m r : ℕ) (δ w t0 : ℝ) (p : Fin r → ℝ) (D : Finset (Fin r → ZMod 2)),
        16 ≤ R → 1 ≤ m → m ≤ R → r ≤ R → 0 < δ → δ < 1 →
        Real.log ((R : ℝ) + 1) ≤ Real.log (1 / δ) → 0 < w →
        (∀ i, 1 / 8 ≤ p i ∧ p i ≤ 3 / 8) →
        (∀ z ∈ D, ∃ a : Fin r → ℝ, IsCertificate (D : Set _) z a ∧ ∑ i, a i ≤ t0) →
        (2 ≤ D.card →
          ∃ pc : Procedure r (Fin r → ZMod 2), pc.IsMeasurable ∧
            (∃ cap : ℕ, ∀ x ∈ D, ∀ ω n,
              ∑ i, (prun (coordMenu r) pc x ω n).calls i ≤ cap) ∧
            ∀ x ∈ D,
              plaw p {ω | ¬ ∃ n, (prun (coordMenu r) pc x ω n).out = some x} ≤
                ENNReal.ofReal (δ / m) ∧
              ENNReal.ofReal w * expCalls (coordMenu r) p pc x ≤
                ENNReal.ofReal (C * w * (t0 * Real.log (1 / δ) + r * Real.log (r + 1) +
                  r * Real.log (1 / δ) / (R : ℝ) ^ 3))) ∧
        (D.card = 1 →
          ∃ pc : Procedure r (Fin r → ZMod 2), pc.IsMeasurable ∧
            ∀ x ∈ D, ∀ ω, (∀ n, ∑ i, (prun (coordMenu r) pc x ω n).calls i = 0) ∧
              ∃ n, (prun (coordMenu r) pc x ω n).out = some x) := by sorry

end InteractionElim.Main
