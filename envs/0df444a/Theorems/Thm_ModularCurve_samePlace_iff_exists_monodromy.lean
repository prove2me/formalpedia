-- Prove2me | Theorems.Thm_ModularCurve_samePlace_iff_exists_monodromy
-- name    : ModularCurve.samePlace_iff_exists_monodromy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e7630490-b841-57a1-ad5b-d275ba655cec
-- title:
--   Places of normalised Hahn-series embeddings differ by monodromy
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $j_0 \in \overline{\mathbb{Q}}$, and let $\psi, \psi'$ be elements of `Emb N j₀`, that is, $\overline{\mathbb{Q}}$-algebra homomorphisms from the field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field, an intermediate field of the Laurent series over $\overline{\mathbb{Q}}$) into the Hahn series $\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ with rational exponents, each sending the distinguished element `jBar N` to $j_0 + t$, where $t$ is the monomial `single 1 1` of exponent $1$ and coefficient $1$. The theorem asserts the equivalence of two conditions. First, `SamePlace ψ.1 ψ'.1`: there is a place $w$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the image of $\overline{\mathbb{Q}}$ and a principal ideal ring) which both $\psi$ and $\psi'$ induce, where $\psi$ induces $w$ when there is a rational $g > 0$ with $(\mathrm{ord}_w x)\,g = \mathrm{order}(\psi\,x)$ for every $x$ (the scaling factor $g$ may differ for $\psi$ and $\psi'$). Second: there is an element $m$ of the subgroup `monodromy` of $\overline{\mathbb{Q}}$-algebra automorphisms of $\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$, namely the image under `hahnTwistHom` of the group `MonoChar` of monoid homomorphisms $\chi : \mathbb{Q} \to \overline{\mathbb{Q}}^{\times}$ (written multiplicatively) with $\chi(1) = 1$, each such $\chi$ acting by scaling the coefficient of exponent $a$ by $\chi(a)$, such that $\psi$ followed by $m$ equals $\psi'$ as algebra homomorphisms.
--
--   This identifies the fibres of the map from normalised Hahn-series expansions at $j_0$ to places of the level-$N$ modular function field: two normalised embeddings induce the same place exactly when they differ by a coefficientwise twist fixing the exponent-$1$ coefficient. It is used in the construction of elliptic points and cyclic-subgroup orbit maps on the modular curve, through [`ModularCurve.exists_elliptic_cycSub_orbitMap_of_props`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap_of_props) and [`ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_samePlace_iff_exists_monodromy.lean

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_HahnSeries_Monodromy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries ModularCurve AlgebraicCurve

theorem ModularCurve.samePlace_iff_exists_monodromy (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (ψ ψ' : Emb N j₀) :
    SamePlace ψ.1 ψ'.1 ↔
      ∃ m ∈ monodromy (AlgebraicClosure ℚ),
        (↑m : HahnSeries ℚ (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ)).comp ψ.1 = ψ'.1 := by sorry
