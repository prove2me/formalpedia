-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_24
-- name    : JainCRERepetition.Cubic.lemma_2_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:26.229875+00:00
-- url     : https://prove2.me/theorems/c465ab0e-6d26-4bea-b035-bd0e6ca674af
-- title:
--   Lemma 2.24 — conditional-marginal budget
-- statement:
--   Let $p(h,z)$ be a probability law and $\chi_{h,z}$ normalized quantum states. Let $W$ be an event determined by $(h,z)$, with probability $p_W>0$, and put $q=p(\cdot\mid W)$ and $\chi_h=\sum_zp(z\mid h)\chi_{h,z}$. Every $q$-supported block has finite divergence and
--
--   $$\mathbb E_{(h,z)\sim q}D(\chi_{h,z}\|\chi_h)\le\log_2(1/p_W)+\log_2|Z|.$$
--
--   The same finiteness and bound hold after taking any corresponding reduced subsystem in both arguments. The conditioning cost charges the answer record $Z$, rather than the alphabet of the fixed history $H$.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 19, Lemma 2.24, Eq. (17); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_24
    {H Z I : Type} [Fintype H] [Fintype Z] [Fintype I]
    [DecidableEq H] [DecidableEq Z] [DecidableEq I]
    (p : Law (H × Z)) (χ : H → Z → Op I) (hχ : ∀ h z, IsState (χ h z))
    (W : H × Z → Prop)
    (hp : 0 < ∑ hz, if W hz then p.p hz else 0) :
    let pW := ∑ hz, if W hz then p.p hz else 0
    let q := fun hz => if W hz then p.p hz / pW else 0
    let χH := fun h => ∑ z, (kernel p.p h z : ℂ) • χ h z
    (∀ h z, 0 < q (h,z) → FiniteD (χ h z) (χH h)) ∧
    (∑ h, ∑ z, q (h,z) * d (χ h z) (χH h)) ≤
      Real.logb 2 (1/pW) + Real.logb 2 (Fintype.card Z) ∧
    (∀ (J E : Type) [Fintype J] [Fintype E] [DecidableEq J] [DecidableEq E]
      (e : I ≃ J × E),
      let reducedχ := fun h z => trR ((χ h z).submatrix e.symm e.symm)
      let reducedH := fun h => trR ((χH h).submatrix e.symm e.symm)
      (∀ h z, 0 < q (h,z) → FiniteD (reducedχ h z) (reducedH h)) ∧
      (∑ h, ∑ z, q (h,z) * d (reducedχ h z) (reducedH h)) ≤
        Real.logb 2 (1/pW) + Real.logb 2 (Fintype.card Z)) := by sorry
end JainCRERepetition.Cubic
