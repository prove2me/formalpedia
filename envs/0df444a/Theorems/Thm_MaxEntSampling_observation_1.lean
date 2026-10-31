-- Prove2me | Theorems.Thm_MaxEntSampling_observation_1
-- name    : MaxEntSampling.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:40.780429+00:00
-- url     : https://prove2.me/theorems/d308d5ee-fc49-4d8c-9503-b9fed69da188
-- title:
--   Observation 1 — $\det(C_{S,S})=\det^s\bigl(\sum_{i\in S}v_iv_i^\top\bigr)$
-- statement:
--   Let $V\in\mathbb R^{d\times n}$ have columns $v_1,\dots,v_n$, let $C=V^\top V$, and let $1\le s\le d$. For every $S\subseteq[n]$ with $|S|=s$,
--
--   $$
--   \det(C_{S,S}) = {\det}^s\Bigl(\sum_{i\in S}v_iv_i^\top\Bigr),
--   $$
--
--   the product of the $s$ largest eigenvalues of $V_SV_S^\top=\sum_{i\in S}v_iv_i^\top$.
--
--   This turns MESP (1) into the formulation (2) over binary vectors, which the rest of the paper relaxes.
--
--   **Formalization Note** $\sum_{i\in S}v_iv_i^\top$ is `PropVolSampling.Reduction.gram V S`; eigenvalues are sorted decreasingly with 0-based indices.
--
--   Differences from the source:
--   - reading: S ⊆ [n] (size not restated) → S.card = s; reason: det^s is the size-s functional and the observation is used for |S| = s in passing from (1) to (2); for |S| < s the identity fails
--   - generalization: C = VᵀV of rank d → any V ∈ ℝ^{d×n}; reason: the identity holds for every factor V; it specializes to the paper's rank-d V
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Observation 1, p.6 (PDF p.6)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Definitions.Def_MaxEntSampling_detTop

open Matrix Finset

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **Observation 1: `det(C_{S,S}) = det^s(Σ_{i∈S} v_i v_iᵀ)`.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Observation 1, p.6 (PDF p.6): "det(C_{S,S}) = det^s(Σ_{i∈S} vi vi^⊤)", where
`C = VᵀV` with `V ∈ ℝ^{d×n}` and `v_i` is the `i`-th column of `V`.

For every `V ∈ ℝ^{d×n}`, every `1 ≤ s ≤ d` and every `S ⊆ [n]` with `|S| = s`, the principal
minor `det((VᵀV)_{S,S})` equals the product of the `s` largest eigenvalues of
`Σ_{i∈S} v_i v_iᵀ = V_S V_Sᵀ`.

**Formalization Note.** `Σ_{i∈S} v_i v_iᵀ` is `PropVolSampling.Reduction.gram V S`
(`= V_S V_Sᵀ`). `|S| = s` is the size of the sets to which the observation is applied (MESP (1)
and (2)); `V` need not have rank `d`. -/
theorem observation_1 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) (hs1 : 1 ≤ s)
    (hsd : s ≤ d) (S : Finset (Fin n)) (hS : S.card = s) :
    ((Vᵀ * V).submatrix (Subtype.val : S → Fin n) Subtype.val).det = detTop s (gram V S) := by sorry

end MaxEntSampling
