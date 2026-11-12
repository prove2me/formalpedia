-- Prove2me | Theorems.Thm_ImpuritySim_lemma_4_3
-- name    : ImpuritySim.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:35:45.017346+00:00
-- url     : https://prove2.me/theorems/6759b864-a434-43d9-87ed-cf1ad7e1b8b0
-- title:
--   Lemma 4.3 — commutator identity $[A_I,H]=B_I+C_I$
-- statement:
--   For a Hamiltonian $H$ in the form (3.15) and every nonempty increasing list $I=(i_1<\dots<i_q)$ of residual-bath modes,
--   $$[A_I,H]=B_I+C_I,\qquad(4.18)$$
--   where $A_I=a_{i_q}\cdots a_{i_1}$,
--   $$B_I=\sum_{i\in I}\sum_{\substack{j:\ell(j)=\ell(i)\\ j\notin I\setminus\{i\}}}\varepsilon_I(i,j)\langle e_j,E_{\ell(i)}e_i\rangle A_{I(i\to j)},\qquad C_I=\sum_{i\in I}\eta_I(i)\sum_{s=1}^{r_{\ell(i)}}\langle u_{\ell(i)s},e_i\rangle G_{\ell(i)s}A_{I\setminus\{i\}},$$
--   $I(i\to j)$ is $I$ with $i$ replaced by $j$, and $\varepsilon_I(i,j),\eta_I(i)\in\{\pm1\}$ are the signs from restoring decreasing order.
--
--   $B_I$ keeps the residual-bath degree and $C_I$ lowers it by one; this triangular structure drives the recursion for $F_q$.
--
--   **Formalization Note** $\varepsilon_I(i,j)=(-1)^{\#\{k\in I\setminus\{i\}\text{ strictly between }i\text{ and }j\}}$, $\eta_I(i)=(-1)^{\#\{k\in I:k>i\}}$; $j$ ranges over residual-bath modes.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - encoding: ε_I(i, j), η_I(i): "the signs arising from restoring the standard decreasing order" → ε_I(i, j) = (−1)^{#{k ∈ I∖{i} : k strictly between i and j}}, η_I(i) = (−1)^{#{k ∈ I : k > i}}; reason: these are the reordering signs of p.23 and App. B.2 written out
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 4.3, Eqs. (4.18)–(4.20), p.22; signs, p.23; proof App. B.2, p.55

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Lemma 4.3 (Commutator identity)**, pp.22–23, of J. Jiang, N. Ju, O. Parekh, C. Rayudu,
A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (4.18)–(4.20).

For an impurity Hamiltonian `H` in the form (3.15) and every nonempty increasing list
`I = (i_1 < ⋯ < i_q)` of residual-bath modes, `[A_I, H] = B_I + C_I` (4.18), where
`B_I = Σ_{i ∈ I} Σ_{j : ℓ(j) = ℓ(i), j ∉ I∖{i}} ε_I(i, j) ⟨e_j, E_{ℓ(i)} e_i⟩ A_{I(i→j)}` (4.19) and
`C_I = Σ_{i ∈ I} η_I(i) Σ_{s=1}^{r_{ℓ(i)}} ⟨u_{ℓ(i)s}, e_i⟩ G_{ℓ(i)s} A_{I∖{i}}` (4.20).

**Formalization Note.** `A_I = a_{i_q} ⋯ a_{i_1}` (`AI`); the signs `ε_I(i, j)`, `η_I(i)` are the
reordering signs of p.23 (`epsSign`, `etaSign`); `I(i→j) = (I∖{i}) ∪ {j}`; `j` ranges over
residual-bath modes. -/
theorem lemma_4_3 {n : ℕ} (F : BandwiseForm n) (I : Finset (Fin n)) (hI : I ⊆ F.bath)
    (hne : I.Nonempty) :
    AI n I * F.H - F.H * AI n I = F.BI I + F.CI I := by sorry

end ImpuritySim
