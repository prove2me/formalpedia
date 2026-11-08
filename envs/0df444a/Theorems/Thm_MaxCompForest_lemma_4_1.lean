-- Prove2me | Theorems.Thm_MaxCompForest_lemma_4_1
-- name    : MaxCompForest.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:51.382531+00:00
-- url     : https://prove2.me/theorems/a18a13af-21ad-4072-9cfd-07076df1c86e
-- title:
--   Lemma 4.1 — conditional trace charge
-- statement:
--   Let $K$ be a real symmetric matrix on a finite index set with $0\preceq K\preceq I$. For every subset $S$ of indices with $K_S\succ0$, put $s=|S|$ and $\ell_j(S)=K_{jS}K_S^{-1}K_{Sj}$. Then $\ell_j(S)\ge0$ for every $j$, and
--   $$
--   \sum_{j}\ell_j(S)=\mathrm{tr}\big(K_S^{-1}(K^2)_S\big)\le s .
--   $$
--   Equality holds if $K$ is an orthogonal projection.
--
--   This bounds the total diagonal mass lost by conditioning on $S$; it powers the exchange argument of the high-marginal recursion.
--
--   Differences from the source:
--   - encoding: $K\in\mathbb R^{m\times m}$, $S\subseteq[m]$ → any finite index type; reason: a finite type is a relabelling of $[m]$
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 4.1, pp.25–26

import Mathlib
import Definitions.Def_MaxCompForest_condLoss
import Definitions.Def_MaxCompForest_onLabels

namespace MaxCompForest

/-- **Lemma 4.1 (Conditional trace charge).**
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), pp.25–26.

**Formalization Note.** `0 ⪯ K ⪯ I` is `K` and `1 − K` positive semidefinite (Mathlib's `PosSemidef` includes
symmetry), and `K_S ≻ 0` is `PosDef`. The index is any finite type. -/
theorem lemma_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) (S : Finset ι)
    (hS : (onLabels K S).PosDef) :
    (∀ j, 0 ≤ condLoss K S j) ∧
      ∑ j, condLoss K S j = ((onLabels K S)⁻¹ * onLabels (K * K) S).trace ∧
      ((onLabels K S)⁻¹ * onLabels (K * K) S).trace ≤ S.card ∧
      (K * K = K → ((onLabels K S)⁻¹ * onLabels (K * K) S).trace = S.card) := by sorry

end MaxCompForest
