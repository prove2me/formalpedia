-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_mem_unitClosure
-- name    : Leopoldt.semilocalGaloisAut_mem_unitClosure
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:22.498772+00:00
-- url     : https://prove2.me/theorems/fe8b831b-01d4-4458-8e64-824f20cd4a14
-- title:
--   The closure of the global units is Galois-stable
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   Let $\overline E=\bigcap_{n\ge 1}\iota(\mathcal O_K^\times)\,U^{p^{n}}\subseteq U$ be the $p$-adic closure of the global units. Then for every $\sigma\in\operatorname{Aut}(K/\mathbb Q)$,
--   $$x\in\overline E\ \Longrightarrow\ \sigma_U(x)\in\overline E .$$
--
--   Thus $\overline E$ is an $\operatorname{Aut}(K/\mathbb Q)$-submodule of $U$, so the Galois group acts on $\overline E$ and on its $\mathbb Z_p$-rank computations, as used in the representation-theoretic treatment of the Leopoldt defect.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.semilocalGaloisAut_mem_unitClosure (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K)
    {x : Leopoldt.SemilocalUnits p K} (hx : x ∈ Leopoldt.unitClosure p K) :
    Leopoldt.semilocalGaloisAut p K σ x ∈ Leopoldt.unitClosure p K := by sorry
