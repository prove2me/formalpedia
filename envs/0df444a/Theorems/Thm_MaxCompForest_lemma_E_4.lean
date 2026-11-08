-- Prove2me | Theorems.Thm_MaxCompForest_lemma_E_4
-- name    : MaxCompForest.lemma_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:02.663472+00:00
-- url     : https://prove2.me/theorems/1c95f0d4-10f5-4889-9858-4cbf92082ca9
-- title:
--   Lemma E.4 — weighted all-low slow-response comparison
-- statement:
--   Let $H$ be a connected loopless multigraph with positive conductances and at most $\nu$ labels per vertex pair, and let $1\le q<|V(H)|$. Suppose that every label $e$ satisfies $K^{(H)}_{ee}<\alpha$, and that $\lambda_{q+1}(N_H)\ge\gamma$ for $0<\gamma\le1$. Let $R_H$ be the slow response at a cutoff $c\in[\gamma/4,\gamma/2]$. For every set $F$ of labels with $|F|\le k$, put
--   $$
--   P_F=C_F^{1/2}B_F^{\top}(D^{-1}+R_H)B_FC_F^{1/2}.
--   $$
--   Then, with $\delta_H=(4/\gamma)\sqrt{2k\nu\alpha}$,
--   $$
--   (1-\delta_H)P_F\preceq K^{(H)}_F\preceq(1+\delta_H)P_F .
--   $$
--   No bound on the conductance ratio is needed, and the families $F$ may be linearly dependent. A relative comparison of this kind controls determinants even when the selected matrix is nearly singular, which an additive error would not.
--
--   Differences from the source:
--   - generalization: “the same cutoff” as Theorem F.1, a certified rational $c\in[\gamma/4,\gamma/2]$ → every real $c\in[\gamma/4,\gamma/2]$; reason: the proof uses only that retained eigenvalues are below $\gamma/2$ and that positive unretained ones are at least $\gamma/4$; the cutoff of Theorem F.1 is one such $c$
--   - encoding: Loewner inequalities $\preceq$ → `PosSemidef` of the two differences; reason: the definition of the order
--   - generalization: positive rational conductances → positive real conductances; reason: the argument uses only positivity; rationality matters only for the machine statements, and rational inputs are a special case
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.4, p.39

import Mathlib
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_K
import Definitions.Def_MaxCompForest_onLabels
import Definitions.Def_MaxCompForest_respForm
import Definitions.Def_MaxCompForest_slowResp
import Definitions.Def_MaxCompForest_PairMult
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma E.4 (Weighted all-low slow-response comparison)**: `(1 − δ_H) P_F ⪯ K^(H)_F ⪯ (1 + δ_H) P_F`,
`δ_H = (4/γ) √(2kνα)`, for every label family `F` with `|F| ≤ k`, dependent families included.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.39.

**Formalization Note.** "The same cutoff as in Theorem F.1" is any `c ∈ [γ/4, γ/2]`: the proof uses only that
retained eigenvalues are below `γ/2` and that positive unretained ones are at least `γ/4`. -/
theorem lemma_E_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : WGraph V E) (hH : H.IsConnected) (q ν k : ℕ) (hq1 : 1 ≤ q)
    (hqn : q < Fintype.card V) (hν : PairMult H ν) (α γ c : ℝ) (hα : ∀ e, K H e e < α)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hlam : γ ≤ lam H (deg H) q) (hc1 : γ / 4 ≤ c) (hc2 : c ≤ γ / 2)
    (F : Finset E) (hF : F.card ≤ k) :
    (onLabels (K H) F - (1 - 4 / γ * Real.sqrt (2 * k * ν * α)) •
        respForm H (deg H) (slowResp H c) F).PosSemidef ∧
      ((1 + 4 / γ * Real.sqrt (2 * k * ν * α)) • respForm H (deg H) (slowResp H c) F -
        onLabels (K H) F).PosSemidef := by sorry

end MaxCompForest
