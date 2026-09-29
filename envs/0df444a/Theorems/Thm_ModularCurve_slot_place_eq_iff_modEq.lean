-- Prove2me | Theorems.Thm_ModularCurve_slot_place_eq_iff_modEq
-- name    : ModularCurve.slot_place_eq_iff_modEq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8abf7cfd-a637-59cd-90d0-f119e5677181
-- title:
--   Places of X₀(N) labelled by pairs (a,b)
-- statement:
--   Let $K$ be a field of characteristic zero (an algebra over $\mathbb{Q}$), let $N$ be a positive natural number, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $N$-th root of unity. Let $a,b,a',b'$ be natural numbers with $a\mid N$, $a'\mid N$ and $a,a'$ nonzero. Work in $F =$ `laurentBaseChange K (modularFunctionFieldFull N)`, the subfield of $K((q))$ generated over $K$ by the coefficientwise images under $\mathbb{Q}\to K$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all $q\mapsto q^d$ substitutions $j(q^d)$ of the $j$-expansion $jq$, for nonzero $d\mid N$. Let $\iota,\iota' : F\to K((q))$ be $K$-algebra maps such that $\iota$ and $\iota'$ both send the generator coming from $j(q)$ to $j(q^N)$, while $\iota$ sends the generator coming from $j(q^N)$ to $j(\zeta^{ba}q^{a^2})$, that is to the image under $q\mapsto q^{a\cdot a}$ of the twist of $j(q)$ whose $k$-th coefficient is multiplied by $\zeta^{(b a)k}$, and $\iota'$ sends it to $j(\zeta^{b'a'}q^{a'^2})$ likewise. Let $w,w'$ be places of $F$ over $K$ (valuation subrings containing $K$, proper, and principal ideal rings) and $\gamma,\gamma'$ positive integers with $w.\mathrm{ord}(x)\,\gamma = \mathrm{order}(\iota x)$ and $w'.\mathrm{ord}(x)\,\gamma' = \mathrm{order}(\iota' x)$ for all $x\in F$, where $\mathrm{ord}$ is the $\mathbb{Z}$-valued valuation attached to the place. Then $w = w'$ if and only if $a = a'$ and $b \equiv b' \pmod{\gcd(a, N/a)}$.
--
--   This is the classical labelling of the cusps of $X_0(N)$ by pairs $(a,b)$ with $a\mid N$ and $b$ taken modulo $\gcd(a,N/a)$, here expressed as a criterion for two places of the function field to coincide in terms of the normalised $q$-expansion embeddings attached to the labels. It is used in the count of the places of negative order at $\bar\jmath$ against the number of cusps and in the production of pairs of places in a fibre of the Hecke correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slot_place_eq_iff_modEq.lean

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.slot_place_eq_iff_modEq (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) [NeZero a] (a' b' : ℕ) (ha' : a' ∣ N) [NeZero a']
    (ι ι' : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (hι'₁ : ι' ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι'₂ : ι' ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a' * a') (qTwist (ζ ^ (b' * a')) (coeffEmb K jq)))
    (w w' : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ γ' : ℤ)
    (hγ : 0 < γ) (hγ' : 0 < γ')
    (hw : ∀ x, w.ord x * γ = (ι x).order) (hw' : ∀ x, w'.ord x * γ' = (ι' x).order) :
    w = w' ↔ a = a' ∧ b ≡ b' [MOD Nat.gcd a (N / a)] := by sorry
