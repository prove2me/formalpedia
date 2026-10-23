-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_lemma_2_11_iii
-- name    : LindbladReach.MinDiss.lemma_2_11_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:36.621098+00:00
-- url     : https://prove2.me/theorems/9b7332cb-e19e-43ca-87ae-06f4403c6ebc
-- title:
--   Lemma 2.11(iii), p. 8 — with |0⟩⟨1| ⊗ I and Z_1 in S, the range of |0_k⟩⟨0_k| is all of D(H)
-- statement:
--   Let $H=\mathbb C^{2^k}$ be the space of $k\ge1$ qubits, and let $S=S^*$ generate a Hörmander system. Suppose $|0\rangle\langle1|\otimes I^{\otimes(k-1)}\in S$ and $Z_1=Z\otimes I^{\otimes(k-1)}\in S$. Then
--   $$D_S(|0_k\rangle\langle0_k|)=\mathcal D(H),$$
--   where $D_S(\rho)=\{\Phi(\rho):\Phi\in\overline{\mathrm{Channel}(S)}\}$ is the range of $\rho$ (Definition 2.9). Both inclusions are part of the statement:
--   - every channel of the closed class maps the pure state $|0_k\rangle\langle0_k|$ to a density;
--   - every density is reached from $|0_k\rangle\langle0_k|$.
--
--   This is the second half of the proof of Theorem 2.12: from the reference state every target can be recreated.
--
--   **Formalization Note** The page prints the jump as "$|0\rangle\langle I|\otimes 1^{k-1}$". This is read as $|0\rangle\langle1|\otimes I^{\otimes(k-1)}$, as in part (i) of the lemma and in Theorem 2.12. $k\ge1$ is added because the page names the first qubit.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 8, Lemma 2.11(iii); range D_S(ρ), Definition 2.9, p. 8

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Lemma 2.11(iii), p. 8: if `|0⟩⟨1| ⊗ I^{⊗(k−1)}` and `Z_1` are in `S`, then
`D_S(|0_k⟩⟨0_k|) = D(H)`. -/
theorem lemma_2_11_iii {k : ℕ} (hk : 0 < k) (S : Set (Mat k)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    (hH : IsHormander S) (ha : ampDamp ⟨0, hk⟩ ∈ S) (hz : dephZ ⟨0, hk⟩ ∈ S) :
    reachSet S (zeroState k) = {ρ | IsDensity ρ} := by sorry

end LindbladReach.MinDiss
