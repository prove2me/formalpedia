-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_sPartDual_eq_single
-- name    : LanglandsTunnell.Converse.sPartDual_eq_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/a9e0a9e1-a050-5986-bb2b-1149797ae7d3
-- title:
--   Dual S-part series with one-point support is a monomial
-- statement:
--   Let $K$ be a number field, $S$ a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, $Ad \colon (S \to \mathbb{Z}) \to \mathbb{C}$ a family of complex coefficients indexed by the integer exponent vectors on $S$, $\mu$ a monoid homomorphism from the unit group of the adele ring of $K$ to $\mathbb{C}^\times$, $s$ a complex number, and $n_0 \colon S \to \mathbb{Z}$ a fixed exponent vector. Assume that $Ad(n) = 0$ for every $n \neq n_0$. Then the dual $S$-part series $$\mathrm{sPartDual}(K, S, Ad, \mu, s) = \sum_{n \colon S \to \mathbb{Z}} Ad(n) \prod_{v \in S} \bigl(\mu(\varpi_v)^{-1} \, (\mathrm{absNorm}\, v)^{1/2 - s}\bigr)^{n_v},$$ an unconditional `tsum` over all exponent vectors, equals the single term $Ad(n_0) \prod_{v \in S} \bigl(\mu(\varpi_v)^{-1} (\mathrm{absNorm}\, v)^{1/2 - s}\bigr)^{n_0(v)}$. Here $\varpi_v =$ `uniformizerIdele K v` is the idele whose finite component at $v$ is the image of a chosen uniformizer of $v$ and whose components elsewhere (including the infinite ones) are $1$, $\mathrm{absNorm}\,v$ is the absolute norm of the ideal underlying $v$, and the complex powers are the usual complex exponentials, with integer exponents $n_v$ giving group powers.
--
--   This is the degenerate evaluation of the dual $S$-part Dirichlet-type series attached to a coefficient family concentrated at one exponent vector: a sum over the lattice $\mathbb{Z}^S$ collapses to a single monomial in the local parameters $\mu(\varpi_v)^{-1} q_v^{1/2-s}$. It serves the construction of converse-theorem data in the Langlands–Tunnell part of the development, and is used by [`LanglandsTunnell.Converse.exists_sPartDual_eq_of_forall_cancel_units`](thm.html#LanglandsTunnell.Converse.exists_sPartDual_eq_of_forall_cancel_units).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_sPartDual_eq_single.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.Converse.sPartDual_eq_single (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (n₀ : ↥S → ℤ)
    (hAd : ∀ n : ↥S → ℤ, n ≠ n₀ → Ad n = 0) :
    sPartDual K S Ad μ s = Ad n₀ * ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n₀ v) := by sorry
