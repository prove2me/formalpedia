-- Prove2me | Theorems.Thm_MazurAdmissible_AdmissibleChain_exists_map_addEquiv
-- name    : MazurAdmissible.AdmissibleChain.exists_map_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2f337813-e9da-5868-89c6-d28155fe0ece
-- title:
--   Transport of admissible chains along an equivariant isomorphism
-- statement:
--   Let $M$ and $M'$ be additive abelian groups, let $p$ be a natural number, and let $\Phi$, $\Phi'$ be `OpenAction` structures on $M$ and $M'$ respectively, that is, homomorphisms $\Phi.\varphi$, $\Phi'.\varphi$ from the group $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ` into the additive automorphism groups of $M$, resp. $M'$, whose kernels are open subsets. Let $e : M \simeq M'$ be an additive isomorphism which intertwines the two actions, i.e. $\Phi'.\varphi(\sigma)(e\,x) = e(\Phi.\varphi(\sigma)\,x)$ for all $\sigma$ and all $x \in M$. Let $c$ be an admissible chain for $p$ and $\Phi$: a number $n$, subgroups $c.\mathrm{step}(i) \subseteq M$ for $i \in \{0,\dots,n\}$ with $c.\mathrm{step}(0) = \bot$, $c.\mathrm{step}(n) = \top$, increasing, tags $c.\mathrm{tag}(i) \in \{\mathrm{true},\mathrm{false}\}$ for $i < n$, each successive quotient $c.\mathrm{step}(i+1)/c.\mathrm{step}(i)$ of cardinality $p$, and for each $i$: if the tag is true then $\Phi.\varphi(\sigma)x - x \in c.\mathrm{step}(i)$ for all $\sigma$ and all $x \in c.\mathrm{step}(i+1)$, while if the tag is false then $\Phi.\varphi(\sigma)x - a\cdot x \in c.\mathrm{step}(i)$ whenever $\zeta \in \overline{\mathbb Q}$ is a primitive $p$-th root of unity, $\sigma\zeta = \zeta^{a}$ with $a \in \mathbb N$, and $x \in c.\mathrm{step}(i+1)$. The conclusion is that there exists an admissible chain $c'$ for $p$ and $\Phi'$ with the same number of true-tagged steps, `filtAlpha c' = filtAlpha c`, and the same length, `filtLength c' = filtLength c`.
--
--   This is the transport lemma for the bookkeeping device of Mazur's filtration argument: admissible chains, with their length and their count of trivial (as opposed to cyclotomic) steps, depend only on the isomorphism class of the Galois module. It is used to move chains between carriers that are isomorphic but not identical, and between two bundled actions on the same carrier, and is cited in the existence results for admissible chains on subgroups and on the Eisenstein-primary torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.lean

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MazurAdmissible

theorem MazurAdmissible.AdmissibleChain.exists_map_addEquiv
    {M : Type*} [AddCommGroup M] {M' : Type*} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c := by sorry
