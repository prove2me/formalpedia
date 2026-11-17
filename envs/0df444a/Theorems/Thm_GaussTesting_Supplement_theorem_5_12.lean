-- Prove2me | Theorems.Thm_GaussTesting_Supplement_theorem_5_12
-- name    : GaussTesting.Supplement.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:28:12.310537+00:00
-- url     : https://prove2.me/theorems/2e8adc10-e2e4-41f4-aa2c-43d2efac629a
-- title:
--   Theorem 5.12 — on $(\bigwedge^\eta\mathbb C^n)^{\otimes3}$ the nonzero eigenvalues of $P=\Pi_{\mathrm{test}}\mathrm{SWAP}^{(2,3)}\Pi_{\mathrm{test}}$ are $(-1)^r/(r+1)$
-- statement:
--   Fix $n$ fermionic modes and a particle number $0\le\eta\le n$, and work in the three-copy $\eta$-particle sector $(\bigwedge^\eta\mathbb C^n)^{\otimes3}$. Let
--
--   $$
--   P=\Pi^{(1,2)}_{\mathrm{test},\mathcal S}\cdot\mathrm{SWAP}^{(2,3)}\cdot\Pi^{(1,2)}_{\mathrm{test},\mathcal S},
--   $$
--
--   where $\Pi_{\mathrm{test},\mathcal S}$ is the projector onto $\ker K$, $K=G^\dagger G$, $G=\sum_j c_j\otimes c_j^\dagger$, acting on copies $1,2$, and $\mathrm{SWAP}^{(2,3)}$ exchanges copies $2$ and $3$. The eigenvalues $p_r$ of $P$ on this sector, indexed by $0\le r\le\min\{\eta,n-\eta\}$, are
--
--   $$
--   p_r=\frac{(-1)^r}{r+1}.
--   $$
--
--   Precisely: a nonzero complex number $\mu$ is an eigenvalue of $P$ on the sector if and only if $\mu=(-1)^r/(r+1)$ for some integer $0\le r\le\min\{\eta,n-\eta\}$. (The remaining eigenvalue is $0$, on the part of the sector outside the range of $\Pi^{(1,2)}_{\mathrm{test},\mathcal S}$.)
--
--   Since the symmetrized Slater test operator agrees with $(\Pi^{(1,2)}_{\mathrm{test},\mathcal S}+2P)/3$ on the symmetric subspace, this gives its nonzero eigenvalues $\tfrac13(1+2p_r)\in[0,5/9]\cup\{1\}$ (Corollary 5.13), the spectral gap $4/9$ used for the Slater tester, independently of $n$ and $\eta$.
--
--   **Formalization Note** $P$ is `slaterSwapOp n`, the sector is `particleSector n η`; $P$ maps the sector into itself, so an eigenvalue on the sector is a $\mu$ with an eigenvector inside the sector. With $\eta\le n$ the natural-number difference $n-\eta$ is the true one.
--
--   Differences from the source:
--   - reading: the eigenvalues p_r of P take the form (−1)^r/(r + 1), with p_r indexed by 0 ≤ r ≤ min{η, n − η} (Lemma 5.8) on a fixed-particle sector (⋀^η ℂⁿ)^{⊗3} → for η ≤ n and μ ≠ 0: μ is an eigenvalue of P on the sector (an eigenvector v ≠ 0 in the sector) iff μ = (−1)^r/(r + 1) for some r ≤ min η (n − η); reason: 'the eigenvalues p_r' ranges over every r of Lemma 5.8, each of which occurs (Lemma 5.6); 0 is excluded because P vanishes off the range of Π_test, which the paper's p_r do not cover
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ; ℋ^{⊗t} → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗t} is ℓ²(Fin t → ι); reason: unitarily the same spaces; the base mission's convention
--   - encoding: three copies ⋀ℂⁿ ⊗ ⋀ℂⁿ ⊗ ⋀ℂⁿ with SWAP^(2,3) : |S₁⟩⊗|S₂⟩⊗|S₃⟩ ↦ |S₁⟩⊗|S₃⟩⊗|S₂⟩ → ℓ²(Fin 3 → Fin n → Fin 2), plain tensor product, SWAP = permVec (Equiv.swap 1 2) on 0-based registers; reason: the paper's ⊗ between copies is ungraded (p.43); the sign (−1)^η of (5.3) belongs to the auxiliary space W
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 5.12, p.49; Lemma 5.8, p.45; Lemma 5.6, p.44; §5.2, pp.42–43

import Definitions.Def_GaussTesting_Supplement_slaterSwapOp

namespace GaussTesting

namespace Supplement

/-- **Theorem 5.12.** On the `η`-particle three-copy sector `(⋀^η ℂⁿ)^{⊗3}` (`η ≤ n`), the eigenvalues
`p_r` of `P = Π^{(1,2)}_{test,𝒮} · SWAP^{(2,3)} · Π^{(1,2)}_{test,𝒮}`, indexed by
`0 ≤ r ≤ min{η, n − η}` as in Lemma 5.8, are `p_r = (−1)^r/(r + 1)`. Stated as the exact nonzero
spectrum: a nonzero `μ` is an eigenvalue of `P` on the sector if and only if `μ = (−1)^r/(r + 1)` for
some `0 ≤ r ≤ min{η, n − η}`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 5.12, p.49; Lemma 5.8, p.45 (the range of `r`);
Lemma 5.6, p.44; §5.2, pp.42–43 (the sector and `P`).

**Formalization Note.**
* `P` preserves the sector (it commutes with the number operator on each register), so an eigenvalue
  of `P` restricted to the sector is a `μ` with an eigenvector `v ≠ 0` inside the sector.
* `0` is excluded because `P` vanishes on the orthogonal complement of the range of `Π_test` in the
  sector; every `p_r` is nonzero. `μ` is complex; the eigenvalues are real since `P` is self-adjoint.
* `η ≤ n` makes the sector nonzero; `n − η` is then the true difference. -/
theorem theorem_5_12 (n η : ℕ) (hη : η ≤ n) (μ : ℂ) (hμ : μ ≠ 0) :
    (∃ v ∈ particleSector n η, v ≠ 0 ∧ slaterSwapOp n v = μ • v) ↔
      ∃ r : ℕ, r ≤ min η (n - η) ∧ μ = (-1 : ℂ) ^ r / ((r : ℂ) + 1) := by sorry

end Supplement

end GaussTesting
