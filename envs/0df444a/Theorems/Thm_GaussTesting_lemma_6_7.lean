-- Prove2me | Theorems.Thm_GaussTesting_lemma_6_7
-- name    : GaussTesting.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:18.119222+00:00
-- url     : https://prove2.me/theorems/0fea52d5-b8b7-4707-8ee7-43f4ad4ae425
-- title:
--   Lemma 6.7 — the seven-register symmetrization of $\Pi_{\mathrm{test},G_b}$ has spectral gap at least $7/45$
-- statement:
--   Let $\mathcal H$ be the $n$-mode bosonic Fock space and $\Pi_{\mathrm{test},G_b}$ the projector onto the top irrep $V_3\subseteq\mathcal H^{\otimes3}$ (§6.1). Then
--
--   $$
--   \Pi^{(7)}_{\mathrm{test},G_b}=\Pi^{(1,\dots,7)}_{\mathrm{sym}}\,\Pi^{(1,2,3)}_{\mathrm{test},G_b}\,\Pi^{(1,\dots,7)}_{\mathrm{sym}}
--   $$
--
--   has spectral gap at least $7/45$: every nonzero point of the spectrum of $I-\Pi^{(7)}_{\mathrm{test},G_b}$ is at least $7/45$, for every $n$.
--
--   Since $7/45>k(k-1)/(m(m-1))=1/7$ for $k=3$, $m=7$, Theorem 3.5 applies with $\alpha=2/135$.
--
--   Differences from the source:
--   - reading: There is a symmetric projector Π_test,G_b on ℋ^{⊗3} such that … → the statement for the specific projector Π_test,G_b of §6.1 (proj onto topIrrep n 3); reason: with an existential the projector onto Sym³(ℋ) (gap 1) would be a trivial witness; the proof is about §6.1's projector
--   - reading: a spectral gap of 7/45 → spectral gap at least 7/45 (HasGapAtLeast, spectrum of I − Ξ); reason: the proof (Lemma 6.12) gives an operator inequality, i.e. a lower bound, and Theorem 3.5 uses only 'at least Δ'
--   - encoding: Π_test,G_b = projector onto the top irrep → projector onto the closed span of {ϕ^{⊗3} : ϕ ∈ G_b}; reason: (6.11)
--   - reading: G_b (resp. G_{b,0}) = the orbit of |0ⁿ⟩ under (zero-mean) bosonic Gaussian unitaries → unit vectors annihilated, coefficientwise, by the transformed annihilators (r_j + i r_{n+j}) + Σ_k (S_{jk} + i S_{n+j,k}) v_k for some S ∈ Sp(2n, ℝ) and r ∈ ℝ²ⁿ (r = 0 for G_{b,0}); reason: ψ = U|0ⁿ⟩ iff U a_j U† ψ = 0 for all j; the equations determine ψ up to scale; Mathlib has no metaplectic representation on ℓ²(ℕⁿ)
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗k} is ℓ²(Fin k → ι); reason: unitarily the same spaces; Lean convention
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Lemma 6.7, p.58; §6.1, p.56

import Definitions.Def_GaussTesting_topIrrep
import Definitions.Def_GaussTesting_xi
import Definitions.Def_GaussTesting_HasGapAtLeast

namespace GaussTesting

/-- **Lemma 6.7 (Spectral gap for bosonic Gaussians).** Let `ℋ` be the `n`-mode bosonic Fock space. For
the three-copy projector `Π_test,G_b` onto the top irrep (§6.1), `1 − Π^{(7)}_test,G_b` has a spectral
gap of (at least) `7/45`, where `Π^{(7)}_test,G_b = Π^{(1,…,7)}_sym Π^{(1,2,3)}_test,G_b Π^{(1,…,7)}_sym`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Lemma 6.7, p.58; §6.1, p.56.

**Formalization Note.** The printed "There is a symmetric projector `Π_test,G_b`" is read as the
specific projector of §6.1 (`proj (topIrrep n 3)`), since the projector onto `Sym³(ℋ)` would witness the
existential trivially; "a spectral gap of `7/45`" is read as "at least `7/45`" (`HasGapAtLeast`), the
form proved (Lemma 6.12) and used (Theorem 3.5). `Π^{(7)} = xi (topIrrep n 3) 4` (`m = 7`). -/
theorem lemma_6_7 (n : ℕ) : HasGapAtLeast (xi (topIrrep n 3) 4) (7 / 45) := by sorry

end GaussTesting
