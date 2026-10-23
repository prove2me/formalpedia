-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_lemma_2_11_ii
-- name    : LindbladReach.MinDiss.lemma_2_11_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:42.436003+00:00
-- url     : https://prove2.me/theorems/f63efc5e-c528-42a1-82b5-40f7293a379f
-- title:
--   Lemma 2.11(ii), p. 8 — if Z_1 ∈ S, then E∞ ⊗ id^{k−1} and E∞^{⊗k} are in the closed class Channel(S)
-- statement:
--   Let $H=\mathbb C^{2^k}$ be the space of $k\ge1$ qubits, and let $S=S^*$ generate a Hörmander system. Suppose $Z_1=Z\otimes I^{\otimes(k-1)}\in S$. Then the conditional expectations
--   $$E_\infty\otimes\mathrm{id}^{k-1}\in\overline{\mathrm{Channel}(S)}\qquad\text{and}\qquad E_\infty^{\otimes k}\in\overline{\mathrm{Channel}(S)} .$$
--   Here $E_\infty\otimes\mathrm{id}^{k-1}$ deletes the matrix entries that are off-diagonal in the first qubit, and $E_\infty^{\otimes k}(\rho)=\operatorname{diag}(\rho)$ is the full pinching in the computational basis.
--
--   A single dephasing jump on one qubit, together with unitary control, therefore yields complete dephasing in the computational basis.
--
--   **Formalization Note** $k\ge1$ is added because the page names the first qubit. $S=S^*$ is the condition $a\in S\Rightarrow a^*\in S$. The first qubit is index `0` of the bit strings.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 8, Lemma 2.11(ii)

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Lemma 2.11(ii), p. 8: if `Z_1 ∈ S`, then `E∞ ⊗ id^{k−1}` and `E∞^{⊗k}` lie in the closed class. -/
theorem lemma_2_11_ii {k : ℕ} (hk : 0 < k) (S : Set (Mat k)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    (hH : IsHormander S) (hz : dephZ ⟨0, hk⟩ ∈ S) :
    pinch ⟨0, hk⟩ ∈ channelClosure S ∧ pinchAll ∈ channelClosure S := by sorry

end LindbladReach.MinDiss
