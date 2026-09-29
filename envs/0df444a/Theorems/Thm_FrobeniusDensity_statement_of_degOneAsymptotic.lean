-- Prove2me | Theorems.Thm_FrobeniusDensity_statement_of_degOneAsymptotic
-- name    : FrobeniusDensity.statement_of_degOneAsymptotic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/be3e1336-20fd-571c-80f8-f0afbd18a342
-- title:
--   Frobenius density from the degree-one prime asymptotic
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$, and assume the predicate [`FrobeniusDensity.DegOneAsymptotic L`](def/FrobeniusDensity_DegOneAsymptotic.html#L33), namely: for every subgroup $H$ of $\operatorname{Gal}(L/\mathbb{Q}) = (L \simeq_{\mathbb{Q}} L)$ and every finite set $S_0 \subseteq \mathbb{N}$, writing $E = L^H$ for the fixed intermediate field of $H$ and $a_\ell$ for the coefficient that is $0$ when $\ell \in S_0$ and otherwise equals `degOneCount E ℓ` — the number of primes $\mathfrak{q}$ of $\mathcal{O}_E$ lying over `ratPrimeIdeal ℓ` with $\#(\mathcal{O}_E/\mathfrak{q}) = \ell$ when $\ell$ is prime, and $0$ otherwise — one has (i) $\sum_\ell a_\ell \ell^{-s}$ summable for every real $s > 1$, and (ii) $s \mapsto \bigl(\sum_\ell a_\ell \ell^{-s}\bigr) + \log(s-1)$ bounded, in the sense of $O(1)$, as $s \to 1^+$. The conclusion is [`FrobeniusDensity.Statement L`](def/TaylorWiles_Primes.html#L72): for every $\sigma \in \operatorname{Gal}(L/\mathbb{Q})$ and every finite $S \subseteq \mathbb{N}$ there is a prime $\ell \notin S$ such that for every prime ideal $Q$ of $\mathcal{O}_L$ lying over `ratPrimeIdeal ℓ` with finite residue ring there exists $k$ coprime to the order of $\sigma$ with $\sigma^k$ conjugate to the arithmetic Frobenius `arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q`.
--
--   This is the group-theoretic half of Frobenius's density theorem: it converts the analytic input, an asymptotic for Dirichlet series counting degree-one primes in all subfields $L^H$, into the existence of infinitely many primes whose Frobenius class meets the set of generators of $\langle\sigma\rangle$. It is used by [`FrobeniusDensity.statement`](thm.html#FrobeniusDensity.statement), which supplies the density statement in the form needed to produce auxiliary primes of Taylor–Wiles type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_statement_of_degOneAsymptotic.lean

import Definitions.Def_FrobeniusDensity_DegOneAsymptotic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem FrobeniusDensity.statement_of_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (hL : FrobeniusDensity.DegOneAsymptotic L) :
    FrobeniusDensity.Statement L := by sorry
