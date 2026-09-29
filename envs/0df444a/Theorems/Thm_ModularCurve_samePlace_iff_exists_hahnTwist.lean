-- Prove2me | Theorems.Thm_ModularCurve_samePlace_iff_exists_hahnTwist
-- name    : ModularCurve.samePlace_iff_exists_hahnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/eb4b6238-1259-5a50-8c99-8b7578c7bb13
-- title:
--   Same induced place iff related by a monodromy twist
-- statement:
--   Fix a nonzero natural number $N$ and an element $j_0$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $F =$ `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb{Q}}((s))$ obtained by base change to $\overline{\mathbb{Q}}$ of the level-$N$ modular function field `modularFunctionFieldFull N`, and let $\bar\jmath =$ `jBar N` be the element of $F$ given by the $q$-expansion of the modular invariant. Let $\psi,\psi'$ be two elements of `Emb N j₀`, i.e. $\overline{\mathbb{Q}}$-algebra homomorphisms from $F$ to the field $\mathbb{H}$ of Hahn series with rational exponents and coefficients in $\overline{\mathbb{Q}}$, each normalised by $\psi(\bar\jmath) = j_0 + s$ (constant term $j_0$ plus the monomial $s^{1}$ with coefficient $1$). The assertion is an equivalence. On one side, `SamePlace` holds for the underlying homomorphisms: there is a place $w$ of $F$ over $\overline{\mathbb{Q}}$ — a valuation subring of $F$, not all of $F$, containing the image of $\overline{\mathbb{Q}}$ and a principal ideal ring — and rationals $g,g'>0$ with $\operatorname{ord}_w(x)\,g = \operatorname{ord}(\psi x)$ and $\operatorname{ord}_w(x)\,g' = \operatorname{ord}(\psi' x)$ for all $x \in F$. On the other side, there is a monoid homomorphism $\chi \colon \mathrm{Multiplicative}\,\mathbb{Q} \to \overline{\mathbb{Q}}^{\times}$ lying in [`HahnSeries.MonoChar`](def/HahnSeries_Monodromy.html#L95), that is, with $\chi(1) = 1$, such that $\psi'(x) = \mathrm{hahnTwist}\,\chi\,(\psi(x))$ for every $x \in F$, where the twist multiplies the coefficient of $s^{a}$ by $\chi(a)$ for each $a \in \mathbb{Q}$.
--
--   This identifies, in function-field terms, the set of normalised Puiseux branches of the modular curve of level $N$ above the point $j = j_0$ of the $j$-line that induce one and the same place: they form a single orbit of the local monodromy group acting by twisting Hahn coefficients by a character trivial on $\mathbb{Z}$. It is used by [`ModularCurve.samePlace_iff_exists_monodromy`](thm.html#ModularCurve.samePlace_iff_exists_monodromy), and rests on the counting of normalised embeddings inducing a given place together with the ramification bound $(\deg)!$ for roots of polynomials with Laurent coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_samePlace_iff_exists_hahnTwist.lean

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_HahnSeries_Monodromy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.samePlace_iff_exists_hahnTwist (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) (ψ ψ' : Emb N j₀) :
    SamePlace ψ.1 ψ'.1 ↔
      ∃ χ ∈ HahnSeries.MonoChar (AlgebraicClosure ℚ),
        ∀ x, ψ'.1 x = HahnSeries.hahnTwist χ (ψ.1 x) := by sorry
