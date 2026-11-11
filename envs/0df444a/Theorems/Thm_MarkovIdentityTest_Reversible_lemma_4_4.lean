-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_4_4
-- name    : MarkovIdentityTest.Reversible.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:07.091198+00:00
-- url     : https://prove2.me/theorems/4cca6d72-7932-43ae-99f7-c1a92795c1b0
-- title:
--   Lemma 4.4 — the capped row signal: $0\le F\le 4$, $\sum_j q_j\kappa_j^2\le 4F$, $F\ge 2H^2(p,q)-d\tau$
-- statement:
--   Let $p,q$ be probability vectors on $d$ coordinates and $\tau\ge0$ with $p_j+\tau>0$ for every $j$. Put $w_j=1/(p_j+\tau)$, the capped weights $v_j=\min\{w_j,3/q_j\}$ ($v_j=w_j$ when $q_j=0$), $\kappa_j=v_jq_j-w_jp_j$ and $F(p,q)=\sum_j(v_jq_j^2+w_jp_j^2-2w_jp_jq_j)$. Then
--   $$0\le F(p,q)\le4,\qquad\sum_jq_j\kappa_j^2\le4F(p,q),\qquad F(p,q)\ge2H^2(p,q)-d\tau,$$
--   with $H^2(p,q)=1-\sum_j\sqrt{p_jq_j}$.
--
--   Capping the weights makes the linear error of the comparison controllable while keeping the rowwise Hellinger signal; §5.4 uses the lemma with $\tau=0$ on supported destinations.
--
--   Differences from the source:
--
--   - generalization: τ = ε/(100n) > 0 (the §4 test parameter) → any τ ≥ 0 with p_j + τ > 0 for every j; reason: the proof uses only these; it covers the §5.4 application with τ = 0 on supported destinations and specializes to τ = ε/(100n)
--   - encoding: d coordinates → Fin d; reason: 0-based indexing
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 20, Lemma 4.4

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_RowStatistics

set_option autoImplicit false

namespace MarkovIdentityTest.Reversible

/-- Lemma 4.4 (Jia, p. 20 / PDF 22), with `w = 1/(p + τ)`. -/
theorem lemma_4_4 (d : ℕ) (p q : Fin d → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (hpτ : ∀ j, 0 < p j + τ) :
    0 ≤ rowSignal (tauWeight τ p) p q ∧ rowSignal (tauWeight τ p) p q ≤ 4 ∧
      ∑ j, q j * clipCoeff (tauWeight τ p) p q j ^ 2 ≤ 4 * rowSignal (tauWeight τ p) p q ∧
      2 * hellingerSq p q - d * τ ≤ rowSignal (tauWeight τ p) p q := by sorry

end MarkovIdentityTest.Reversible
