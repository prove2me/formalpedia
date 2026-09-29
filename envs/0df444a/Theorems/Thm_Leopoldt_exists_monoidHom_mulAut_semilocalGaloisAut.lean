-- Prove2me | Theorems.Thm_Leopoldt_exists_monoidHom_mulAut_semilocalGaloisAut
-- name    : Leopoldt.exists_monoidHom_mulAut_semilocalGaloisAut
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:35.153173+00:00
-- url     : https://prove2.me/theorems/c5aea40a-94ee-43fd-b7e6-9e0cfbfc8c6f
-- title:
--   The Galois action on semilocal units as a homomorphism to $\mathrm{Aut}(U)$
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   There is a group homomorphism
--   $$\rho:\ \operatorname{Aut}(K/\mathbb Q)\longrightarrow\operatorname{Aut}(U)$$
--   with $\rho(\sigma)=\sigma_U$ for every $\sigma$.
--
--   This packages the action of $\operatorname{Aut}(K/\mathbb Q)$ (equal to $\operatorname{Gal}(K/\mathbb Q)$ when $K/\mathbb Q$ is Galois) on the semilocal units as a representation, the starting point for decomposing $U$ and $\overline E$ into isotypic components (e.g. the $\pm$-parts under complex conjugation for CM fields).
--
--   **Formalization Note** $\operatorname{Aut}(U)$ is Mathlib's `MulAut`, whose multiplication is composition: $f\cdot g=f\circ g$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.exists_monoidHom_mulAut_semilocalGaloisAut (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    ∃ φ : (K ≃ₐ[ℚ] K) →* MulAut (Leopoldt.SemilocalUnits p K),
      ∀ σ, φ σ = Leopoldt.semilocalGaloisAut p K σ := by sorry
