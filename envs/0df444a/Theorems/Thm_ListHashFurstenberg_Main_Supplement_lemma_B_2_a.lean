-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_Supplement_lemma_B_2_a
-- name    : ListHashFurstenberg.Main.Supplement.lemma_B_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:58:59.515092+00:00
-- url     : https://prove2.me/theorems/a9d85c4d-d4c0-449d-aa9a-7d681a2215f0
-- title:
--   Lemma B.2(a) — surjective covering bound
-- statement:
--   Let $F$ be a finite field of order $q$, let $u,\ell\ge0$ be integers with $\ell\le u$, and let $S\subseteq F^u$ satisfy $|S|<q^u$. Define $\alpha=1-|S|/q^u$, so $0<\alpha\le1$. For $h:F^u\to F^\ell$ uniformly random among surjective linear maps,
--
--   $$\Pr[h(S)\ne F^\ell]\le\alpha^{\,u-\ell-\log_2\ell-\log_2\log_2q+\log_2\log_2(1/\alpha)}.$$
--
--   The statement includes $S=\varnothing$ and $\ell=0$, with the total logarithm convention specified below. This covering estimate is a supporting result for the tail bound in Theorem B.3.
--
--   Differences from the source:
--   - encoding: finite fields F_q and coordinate spaces F_q^u → an arbitrary finite field F with q = Fintype.card F and vectors Fin u → F; reason: every prime-power field is included, with exactly the same finite sets and uniform maps
--   - encoding: uniformly random surjective linear map and its failure to cover the codomain → the published probSurj applied to h image S ≠ Set.univ; reason: ℓ ≤ u guarantees that surjections exist; the existing conditional law has precisely the finite uniform-surjection distribution here
--   - encoding: the logarithmic expression at ℓ = 0 or α = 1 is not explicitly assigned a value → Mathlib total logarithm with logb 2 0 = 0 and Real.rpow; reason: the inequality remains valid at both boundaries: nonempty S covers the zero-dimensional codomain; empty S has α = 1 and bound 1
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, STOC 2027 submission #1578 (October 2026), Lemma B.2(a), printed p.34 = PDF p.34; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1578.pdf; SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_SurjLaw

namespace ListHashFurstenberg.Main.Supplement

/-- Lemma B.2(a), pp.34–35. Includes ℓ = 0 and the empty set; logb at zero
uses Mathlib's total real logarithm, with the inequality still valid in both cases. -/
theorem lemma_B_2_a (F : Type*) [Field F] [Fintype F]
    (u ℓ : ℕ) (hℓu : ℓ ≤ u) (S : Finset (Fin u → F))
    (hcard : S.card < Fintype.card F ^ u) :
    let q : ℝ := Fintype.card F
    let α : ℝ := 1 - (S.card : ℝ) / q ^ u
    ListHashFurstenberg.Main.probSurj F (Fin u → F) ℓ
      (fun h => h '' (S : Set (Fin u → F)) ≠ Set.univ) ≤
      Real.rpow α ((u : ℝ) - (ℓ : ℝ) - Real.logb 2 (ℓ : ℝ) -
        Real.logb 2 (Real.logb 2 q) + Real.logb 2 (Real.logb 2 (1 / α))) := by sorry

end ListHashFurstenberg.Main.Supplement
