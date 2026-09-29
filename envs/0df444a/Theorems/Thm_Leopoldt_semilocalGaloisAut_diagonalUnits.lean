-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_diagonalUnits
-- name    : Leopoldt.semilocalGaloisAut_diagonalUnits
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:25.909096+00:00
-- url     : https://prove2.me/theorems/b2aa46ed-29d3-4d72-8f11-abd933a9d997
-- title:
--   Galois equivariance of the diagonal embedding of global units
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   Let $\iota:\mathcal O_K^\times\to U$ be the diagonal embedding of the global units. Then for every $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ and every global unit $\varepsilon\in\mathcal O_K^\times$,
--   $$\sigma_U\big(\iota(\varepsilon)\big)=\iota\big(\sigma(\varepsilon)\big),$$
--   where $\sigma(\varepsilon)$ is the image of $\varepsilon$ under the restriction of $\sigma$ to $\mathcal O_K$.
--
--   That is, $\iota$ is $\operatorname{Aut}(K/\mathbb Q)$-equivariant; this is what makes the $p$-adic closure $\overline E$ of the global units a Galois-stable subgroup of $U$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.semilocalGaloisAut_diagonalUnits (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (ε : (𝓞 K)ˣ) :
    Leopoldt.semilocalGaloisAut p K σ (Leopoldt.diagonalUnits p K ε) =
      Leopoldt.diagonalUnits p K (Units.map (RingOfIntegers.mapRingHom (σ : K →+* K)).toMonoidHom ε) := by sorry
