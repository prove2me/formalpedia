-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_5_4
-- name    : GraphTensorCP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:07.583118+00:00
-- url     : https://prove2.me/theorems/2610b53a-c8aa-47c2-8b12-bbf5e368b29c
-- title:
--   Lemma 5.4 — path restriction $E^{(q)}_{i,j}\preceq E^{(q)}_{i,k}\otimes_K E^{(q)}_{k,j}$ and $P^{(\phi)}_{i,j}\le P^{(\phi)}_{i,k}+P^{(\phi)}_{k,j}$
-- statement:
--   Let $n\ge2$ and let $\mathbb F$ be any field. For every three distinct vertices $i,j,k$, every positive integer $q$ and every $\phi\in\Phi_{n,\mathbb F}$,
--
--   $$E^{(q)}_{i,j}\preceq E^{(q)}_{i,k}\otimes_K E^{(q)}_{k,j},\qquad P^{(\phi)}_{i,j}\le P^{(\phi)}_{i,k}+P^{(\phi)}_{k,j}.$$
--
--   An edge resource can be routed through an intermediate vertex; these are the path constraints of $U^\Delta_{\mathrm{CP}}$.
--
--   **Formalization Note** $\preceq$ is `MME.TensorObj.Restrict` and $\otimes_K$ is `MME.TensorObj.kron`.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: $E^{(q)}_{i,j}$ in coordinates → `edgeTensor K i j q` $=\mathsf{WT}$ of the single-edge dimension matrix; reason: same tensor up to coordinates within legs
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 5.4, p.47 (§5 preamble: n ≥ 2, F arbitrary)

import Mathlib
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Lemma 5.4** (spectral triangle inequalities), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.47 (standing assumptions of §5: n ≥ 2,
F arbitrary):
"For every three distinct vertices i, j, k, every positive integer q, and every ϕ ∈ Φ_{n,F},
E^{(q)}_{i,j} ⪯ E^{(q)}_{i,k} ⊗_K E^{(q)}_{k,j}, P^{(ϕ)}_{i,j} ≤ P^{(ϕ)}_{i,k} + P^{(ϕ)}_{k,j}."

**Formalization Note.** `⪯` is `MME.TensorObj.Restrict`, `⊗_K` is `MME.TensorObj.kron`. The first
clause does not involve `ϕ`; the second holds for every spectral point. -/
theorem lemma_5_4 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (i j k : Fin n) (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (q : ℕ) (hq : 0 < q) :
    MME.TensorObj.Restrict (edgeTensor K i j q)
        (MME.TensorObj.kron (edgeTensor K i k q) (edgeTensor K k j q)) ∧
      ∀ φ : Spec K n hn, specWeight φ i j ≤ specWeight φ i k + specWeight φ k j := by sorry

end GraphTensorCP
