-- Prove2me | Theorems.Thm_ImpuritySim_lemma_A_1
-- name    : ImpuritySim.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:31:29.421652+00:00
-- url     : https://prove2.me/theorems/5ea25667-ec3b-42e4-89ba-20b7e3b3e0c5
-- title:
--   Lemma A.1 — canonical form $Q=-\alpha I+\sum_q\lambda_qa_q^\dagger a_q$, $0\le\lambda_q\le\|h\|$, of a quadratic Majorana Hamiltonian
-- statement:
--   Let $r\le n$ and let $h\in\mathbb R^{2r\times2r}$ be real antisymmetric. For the quadratic Hamiltonian
--   $$Q=\frac i4\sum_{j,k=1}^{2r}h_{jk}\gamma_j\gamma_k$$
--   on $n$ modes there are a real orthogonal $2r\times2r$ matrix $G$ and numbers $\lambda_1,\dots,\lambda_r$ such that, with the rotated Majoranas $\tilde\gamma_j=\sum_sG_{sj}\gamma_s$ and $a_q=(\tilde\gamma_{2q-1}+i\tilde\gamma_{2q})/2$,
--
--   1. the $a_q$ satisfy the canonical anticommutation relations $\{a_p,a_q^\dagger\}=\delta_{pq}I$, $\{a_p,a_q\}=0$;
--   2. $0\le\lambda_q\le\|h\|$ for every $q$;
--   3. $$Q=-\alpha I+\sum_{q=1}^r\lambda_qa_q^\dagger a_q,\qquad \alpha=\sum_{q=1}^r\frac{\lambda_q}2.\qquad(A.1)$$
--
--   Applied to the bath part of $H_0$ this produces the diagonal bath matrix $E_0$ with $0\le E_0\le J$ of the hybridization form (2.13).
--
--   **Formalization Note** $\|h\|$ is the spectral norm. The $\alpha$ here is the constant of (A.1), not the energy shift of (1.1).
--
--   Differences from the source:
--   - reading: "one can choose annihilation operators a_1, …, a_r" → a_q = (γ̃_{2q−1} + iγ̃_{2q})/2 with γ̃_j = Σ_s G_{sj} γ_s for a real orthogonal G, and the CAR (2.1) stated; reason: the proof (A.2)–(A.3) constructs them this way and App. A needs them to be combinations of the given Majoranas; this is the stronger reading
--   - encoding: γ_1, …, γ_{2r}; modes 1, …, r → the first 2r Jordan–Wigner generators of the n-mode register (FermiCap.Gaussian.majorana), 0-based; reason: the paper's representation (2.4); index shift only
--   - encoding: ∥h∥ → specNorm h, the L2 operator norm; reason: ∥·∥ is the operator norm; same value
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma A.1, Eq. (A.1), p.52; proof (A.2)–(A.3), pp.52–53

import Mathlib
import Definitions.Def_ImpuritySim_Fermion

open Matrix

namespace ImpuritySim

/-- **Lemma A.1 (Canonical form of a quadratic Hamiltonian)**, p.52, of J. Jiang, N. Ju,
O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (A.1).

Let `r ≤ n` and let `h` be a real antisymmetric `2r × 2r` matrix. For the quadratic Hamiltonian
`Q = (i/4) Σ_{j,k=1}^{2r} h_{jk} γ_j γ_k` on `n` modes there are a real orthogonal `G` and
`λ_1, …, λ_r` with `0 ≤ λ_q ≤ ‖h‖` such that the operators `a_q = (γ̃_{2q−1} + iγ̃_{2q})/2`, built
from the rotated Majoranas `γ̃_j = Σ_s G_{sj} γ_s`, satisfy the canonical anticommutation relations
(2.1) and `Q = −αI + Σ_q λ_q a_q† a_q` with `α = Σ_q λ_q / 2`.

**Formalization Note.**
* "One can choose annihilation operators `a_1, …, a_r`" is read as the canonical family obtained
  from an orthogonal rotation of `γ_1, …, γ_{2r}`, as in the proof (A.2)–(A.3); the CAR are stated.
* Majoranas are 0-based (`γ_j` is `gamma n ⟨j − 1, _⟩`), and `γ_1, …, γ_{2r}` are the first `2r`
  Majoranas of the `n`-mode register; `a_q` is `a ⟨q − 1, _⟩`.
* `‖h‖` is the spectral norm (`specNorm`). The `α` here is the constant of (A.1), not the energy
  shift of (1.1). -/
theorem lemma_A_1 (n r : ℕ) (hrn : r ≤ n) (h : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ)
    (hanti : hᵀ = -h) :
    ∃ (G : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (lam : Fin r → ℝ),
      G ∈ Matrix.orthogonalGroup (Fin (2 * r)) ℝ ∧
      (∀ q, 0 ≤ lam q ∧ lam q ≤ specNorm h) ∧
      let emb : Fin (2 * r) → Fin (2 * n) := fun j => ⟨j.val, by omega⟩
      let gt : Fin (2 * r) → FermiCap.Gaussian.Op n :=
        fun j => ∑ s, ((G s j : ℝ) : ℂ) • gamma n (emb s)
      let a : Fin r → FermiCap.Gaussian.Op n :=
        fun q => (1 / 2 : ℂ) • (gt ⟨2 * q.val, by omega⟩ + Complex.I • gt ⟨2 * q.val + 1, by omega⟩)
      (∀ p q, a p * (a q)ᴴ + (a q)ᴴ * a p = if p = q then 1 else 0) ∧
      (∀ p q, a p * a q + a q * a p = 0) ∧
      (Complex.I / 4) • ∑ j, ∑ k, ((h j k : ℝ) : ℂ) • (gamma n (emb j) * gamma n (emb k)) =
        (-(((∑ q, lam q) / 2 : ℝ) : ℂ)) • (1 : FermiCap.Gaussian.Op n) +
          ∑ q, ((lam q : ℝ) : ℂ) • ((a q)ᴴ * a q) := by sorry

end ImpuritySim
