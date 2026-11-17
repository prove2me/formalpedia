-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_E_1
-- name    : HoneycombCodes.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:41:24.606171+00:00
-- url     : https://prove2.me/theorems/f4e79353-2389-4b44-92c3-f21c140f9d6e
-- title:
--   Theorem E.1 — exact Horn realization of every binary channel on $\mathbb C^d$ in $\mathcal K_{2d}$, isospectral with traces $1/2$
-- statement:
--   For every pair of density matrices $\rho_0,\rho_1$ on $\mathbb C^d$ there is a pair $(K,L)\in\mathcal K_{2d}$ such that
--
--   $$
--   \Phi_{ch}(K,L)=\chi(\rho_0,\rho_1),\qquad \Gamma_{ch}(K,L)=1-2p_e(\rho_0,\rho_1).
--   $$
--
--   Moreover, $K$ and $L$ can be chosen isospectral, with $\operatorname{tr}K=\operatorname{tr}L=1/2$.
--
--   Here $\chi(\rho_0,\rho_1)=S(\bar\rho)-\tfrac12(S(\rho_0)+S(\rho_1))$ is the uniform-prior Holevo information and $p_e(\rho_0,\rho_1)=\tfrac12\operatorname{tr}(\rho_0\bar\rho^{-1/2}\rho_1\bar\rho^{-1/2})$, $\bar\rho=(\rho_0+\rho_1)/2$, the uniform-prior PGM bit error. Every finite-dimensional binary channel is thus reproduced, with the same Holevo information and PGM error, by a Horn pair of twice the dimension.
--
--   Differences from the source:
--
--   - encoding: $\chi$, $p_e$ → the published `PrettyGoodCriterion.holevoUniform`, `PrettyGoodCriterion.pgmBitErrorUniform`; reason: the same quantities (139)–(140)
--   - encoding: "isospectral" → equal characteristic polynomials; reason: for Hermitian matrices this is equality of spectra with multiplicities
--   - encoding: $\mathcal K_{2d}$ → matrices indexed by `Fin (2 * d)`; reason: Lean convention
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. E.1, Theorem E.1, eq. (141), p.66 (PDF 68)

import Mathlib
import Definitions.Def_HoneycombCodes_Supplement_kappaCh

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- **Theorem E.1 (Exact Horn realization)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework
for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.66 (PDF 68). For every pair of
density matrices `ρ₀, ρ₁` on `ℂ^d` there is `(K, L) ∈ K_{2d}` with `Φ_ch(K, L) = χ(ρ₀, ρ₁)` and
`Γ_ch(K, L) = 1 − 2 p_e(ρ₀, ρ₁)` (141); moreover `K` and `L` can be chosen isospectral, with
`tr K = tr L = 1/2`.

**Formalization Note.** `χ` and `p_e` are the published `PrettyGoodCriterion.holevoUniform` and
`PrettyGoodCriterion.pgmBitErrorUniform` (uniform prior, (139)–(140)). `K_{2d}` uses matrices of size
`2d` (`Fin (2 * d)`). Isospectral means equal spectra with multiplicities, stated as equal
characteristic polynomials (both matrices are Hermitian). -/
theorem theorem_E_1 (d : ℕ) (ρ : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hρ : ∀ b, IsDensity (ρ b)) :
    ∃ K L : Matrix (Fin (2 * d)) (Fin (2 * d)) ℂ, InKset (2 * d) K L ∧
      PhiCh K L = PrettyGoodCriterion.holevoUniform ρ ∧
      GammaCh K L = 1 - 2 * PrettyGoodCriterion.pgmBitErrorUniform ρ ∧
      K.charpoly = L.charpoly ∧ K.trace = 1 / 2 ∧ L.trace = 1 / 2 := by sorry

end HoneycombCodes.Supplement
