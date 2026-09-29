-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_one
-- name    : Leopoldt.semilocalGaloisAut_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:13.94597+00:00
-- url     : https://prove2.me/theorems/d1bf5f40-914a-4dbe-9d0f-f7afabb0c1f8
-- title:
--   The identity automorphism acts trivially on semilocal units
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   For the identity automorphism $1\in\operatorname{Aut}(K/\mathbb Q)$,
--   $$1_U=\mathrm{id}_U .$$
--
--   This is the unit axiom of the action of $\operatorname{Aut}(K/\mathbb Q)$ on $U$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.semilocalGaloisAut_one (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Leopoldt.semilocalGaloisAut p K 1 = MulEquiv.refl (Leopoldt.SemilocalUnits p K) := by sorry
