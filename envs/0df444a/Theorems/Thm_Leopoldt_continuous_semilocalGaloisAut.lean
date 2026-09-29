-- Prove2me | Theorems.Thm_Leopoldt_continuous_semilocalGaloisAut
-- name    : Leopoldt.continuous_semilocalGaloisAut
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:14.941966+00:00
-- url     : https://prove2.me/theorems/ca74b20a-0be6-47e9-99dd-97248dd5c6b3
-- title:
--   Continuity of the Galois action on semilocal units
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   **Theorem.** For every $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ the automorphism
--   $$\sigma_U:\ U\longrightarrow U$$
--   is continuous.
--
--   Together with the group-action property (so that $\sigma_U^{-1}=(\sigma^{-1})_U$ is continuous too) this makes $\sigma_U$ a topological group automorphism, so the action preserves closed subgroups, $\mathbb Z_p$-ranks and continuous injections $\mathbb Z_p^n\hookrightarrow U$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.continuous_semilocalGaloisAut (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) :
    Continuous (Leopoldt.semilocalGaloisAut p K σ) := by sorry
