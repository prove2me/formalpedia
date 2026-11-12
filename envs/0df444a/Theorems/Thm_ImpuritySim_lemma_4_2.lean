-- Prove2me | Theorems.Thm_ImpuritySim_lemma_4_2
-- name    : ImpuritySim.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:08.586133+00:00
-- url     : https://prove2.me/theorems/cb23b5c7-e373-4a97-b8c5-5f6930f75851
-- title:
--   Lemma 4.2 — $[H,a_i]=-\sum_{\ell(j)=\ell(i)}\langle e_j,E_{\ell(i)}e_i\rangle a_j-\sum_s\langle u_{\ell(i)s},e_i\rangle G_{\ell(i)s}$
-- statement:
--   For a Hamiltonian $H$ in the form (3.15) and every residual-bath mode $a_i$,
--   $$[H,a_i]=-\sum_{j:\ell(j)=\ell(i)}\langle e_j,E_{\ell(i)}e_i\rangle a_j-\sum_s\langle u_{\ell(i)s},e_i\rangle G_{\ell(i)s},\qquad(4.14)$$
--   where $j$ ranges over the residual-bath modes of the band of $i$. In particular, $[H,a_i]$ does not increase the degree in the residual-bath operators.
--
--   This is the single-mode commutator from which the commutator identity (Lemma 4.3) is assembled.
--
--   **Formalization Note** $\langle e_j,Ee_i\rangle=E_{ji}$ and $\langle u,e_i\rangle=\overline{u_i}$.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - reading: "In particular, [H, a_i] does not increase the degree in the residual-bath operators" → no separate clause; read off the right-hand side of (4.14), which is linear in the a_j and the G_{ℓs}; reason: the sentence describes the shape of (4.14)
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 4.2, Eq. (4.14), p.22

import Mathlib
import Definitions.Def_ImpuritySim_BandwiseForm

open Matrix

namespace ImpuritySim

/-- **Lemma 4.2**, p.22, of J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time
classical and quantum simulation of quantum impurity models*, arXiv:2610.02167 (held version,
sha256 88d2a4e6…f0fff9b2), Eq. (4.14).

For an impurity Hamiltonian `H` in the form (3.15) and any residual-bath mode `a_i`,
`[H, a_i] = − Σ_{j : ℓ(j) = ℓ(i)} ⟨e_j, E_{ℓ(i)} e_i⟩ a_j − Σ_s ⟨u_{ℓ(i)s}, e_i⟩ G_{ℓ(i)s}`.
In particular, `[H, a_i]` does not increase the degree in the residual-bath operators.

**Formalization Note.** `j` ranges over the residual-bath modes of band `ℓ(i)`;
`⟨e_j, E e_i⟩ = E j i` and `⟨u, e_i⟩ = conj(u_i)`. The "in particular" sentence is read off the
right-hand side, which is linear in the bath annihilators `a_j` and the enlarged-impurity operators
`G_{ℓs}`; it is not a separate clause. -/
theorem lemma_4_2 {n : ℕ} (F : BandwiseForm n) (i : Fin n) (hi : i ∈ F.bath) :
    F.H * GaussTesting.annihilator n i - GaussTesting.annihilator n i * F.H =
      -(∑ j ∈ F.bath.filter (fun j => F.band j = F.band i), F.E j i • GaussTesting.annihilator n j) -
        ∑ s : Fin (F.r (F.band i)), star (F.u (F.band i) s i) • F.G (F.band i) s := by sorry

end ImpuritySim
