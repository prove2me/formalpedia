-- Prove2me | Theorems.Thm_ImpuritySim_lemma_3_1
-- name    : ImpuritySim.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:30:49.211852+00:00
-- url     : https://prove2.me/theorems/29691cf5-2a79-401b-bbe6-ee75527dddcc
-- title:
--   Lemma 3.1 — Krylov shells have $\dim W_{*d}\le2m$ and $E_*W_{*d}\subseteq W_{*,d-1}\oplus W_{*d}\oplus W_{*,d+1}$
-- statement:
--   Let $E_*$ be a Hermitian operator on a finite-dimensional complex inner-product space $W_*$, let $\mu_{1*},\dots,\mu_{2m*}\in W_*$, and let $W_{*d}$ be the Krylov shells (3.5). Then
--
--   1. $\dim W_{*d}\le2m$ for every $d\ge0$;
--   2. $$E_*W_{*d}\subseteq W_{*,d-1}\oplus W_{*d}\oplus W_{*,d+1},\qquad W_{*,-1}=\{0\};\qquad(3.7)$$
--   3. consequently $\langle v,E_*u\rangle=0$ whenever $u\in W_{*d}$, $v\in W_{*d'}$ and $|d-d'|\ge2$: in an orthonormal basis ordered by shells, $V^\dagger E_*V$ is block-tridiagonal (3.2).
--
--   This one-dimensional structure is what makes the bandwise Krylov basis useful: each bath block couples only to its neighbours.
--
--   **Formalization Note** The block-tridiagonal form of $V^\dagger E_*V$ is stated basis-free, as the vanishing of matrix elements between shells at distance at least two (in both orders).
--
--   Differences from the source:
--   - encoding: E_* a Hermitian matrix on a subspace W_* of the bath single-particle space → a self-adjoint linear map on an arbitrary finite-dimensional complex inner-product space; reason: W_* is such a space; same instances
--   - encoding: "V†E_*V has the block-tridiagonal form in Eq. (3.2)" → ⟨v, E u⟩ = 0 and ⟨u, E v⟩ = 0 for u ∈ W_{*d}, v ∈ W_{*d'}, d + 2 ≤ d'; reason: the basis-free content of (3.2) for a basis ordered by shells
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 3.1, Eq. (3.7), p.15; (3.2), p.13; (3.4)–(3.5), p.15

import Mathlib
import Definitions.Def_ImpuritySim_Krylov

open scoped InnerProductSpace

namespace ImpuritySim

/-- **Lemma 3.1 (One-dimensional structure)**, p.15, of J. Jiang, N. Ju, O. Parekh, C. Rayudu,
A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (3.7), with (3.2), (3.4), (3.5).

Let `E∗` be a Hermitian (self-adjoint) operator on a finite-dimensional complex inner-product space
`W∗` and `μ_1, …, μ_{2m} ∈ W∗`. Then the Krylov shells `W∗d` satisfy
1. `dim W∗d ≤ 2m` for all `d ≥ 0`;
2. `E∗ W∗d ⊆ W∗,d−1 ⊕ W∗d ⊕ W∗,d+1` (with `W∗,−1 = {0}`) (3.7);
3. hence `E∗` is block-tridiagonal with respect to the shells: `⟨v, E∗u⟩ = 0` whenever `u ∈ W∗d`,
   `v ∈ W∗d'` and `|d − d'| ≥ 2` (the form (3.2) of `V†E∗V`).

**Formalization Note.** The ambient space is `W∗`; `shell E μ d` is `W∗d` (3.5). The
block-tridiagonal form of `V†E∗V` for an orthonormal basis ordered by shells is stated basis-free as
the vanishing of the matrix elements between shells at distance `≥ 2` (both orders). -/
theorem lemma_3_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (m : ℕ) (E : V →ₗ[ℂ] V) (hE : E.IsSymmetric) (μ : Fin (2 * m) → V) :
    (∀ d, Module.finrank ℂ (shell E μ d) ≤ 2 * m) ∧
    (∀ u ∈ shell E μ 0, E u ∈ shell E μ 0 ⊔ shell E μ 1) ∧
    (∀ d, ∀ u ∈ shell E μ (d + 1), E u ∈ shell E μ d ⊔ shell E μ (d + 1) ⊔ shell E μ (d + 2)) ∧
    (∀ d d', d + 2 ≤ d' → ∀ u ∈ shell E μ d, ∀ v ∈ shell E μ d',
      ⟪v, E u⟫_ℂ = 0 ∧ ⟪u, E v⟫_ℂ = 0) := by sorry

end ImpuritySim
