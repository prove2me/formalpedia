-- Prove2me | Theorems.Thm_Leopoldt_semilocalGaloisAut_mul
-- name    : Leopoldt.semilocalGaloisAut_mul
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:49:14.365645+00:00
-- url     : https://prove2.me/theorems/3bb9e2b9-a135-488d-a101-be5191a21064
-- title:
--   The Galois action on semilocal units is multiplicative in $\sigma$
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, $\mathcal P$ the set of primes of $\mathcal O_K$ above $p$, and $U=\prod_{v\in\mathcal P}\mathcal O_v^\times$ the group of semilocal units at $p$ with its product (profinite) topology. For $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ let $\sigma_U:U\to U$ be the Galois action on semilocal units, $(\sigma_U x)_w=\sigma(x_{\sigma^{-1}w})$, where $\sigma:K_{\sigma^{-1}w}\xrightarrow{\sim}K_w$ is the continuous extension of $\sigma$ to completions (definition `Def_LeopoldtGaloisAction`).
--
--   For all $\sigma,\tau\in\operatorname{Aut}(K/\mathbb Q)$,
--   $$(\sigma\tau)_U=\sigma_U\circ\tau_U ,$$
--   where $\sigma\tau$ denotes the composite $x\mapsto\sigma(\tau(x))$.
--
--   Together with $1_U=\mathrm{id}_U$ this says that $\sigma\mapsto\sigma_U$ is a (left) action of $\operatorname{Aut}(K/\mathbb Q)$ on $U$ by group automorphisms.
--
--   **Formalization Note** In Lean, `e.trans f` is the composite "first `e`, then `f`", so $\sigma_U\circ\tau_U$ is written `(semilocalGaloisAut p K τ).trans (semilocalGaloisAut p K σ)`, and `σ * τ` in `K ≃ₐ[ℚ] K` is $x\mapsto\sigma(\tau x)$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (the action of Gal(K/Q) on K_p = K ⊗ Q_p, on U and on Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (Prop. 8.1–8.2 and the discussion of conjugate valuations: an automorphism σ induces isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtGaloisAction

open NumberField

theorem Leopoldt.semilocalGaloisAut_mul (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) :
    Leopoldt.semilocalGaloisAut p K (σ * τ) =
      (Leopoldt.semilocalGaloisAut p K τ).trans (Leopoldt.semilocalGaloisAut p K σ) := by sorry
