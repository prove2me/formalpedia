-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar
-- name    : HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/74864d92-7078-5a8d-993f-1e0bb2ae170c
-- title:
--   Eisenstein identity T_ℓ(χ∘ d)=(ℓ+1)(χ∘ d) for ℓ∤ N
-- statement:
--   Fix a natural number $N$ and a nonzero natural number $\ell$, an additive abelian group $A$, a proof $h\ell$ that $\ell$ is prime and a proof $h\ell N$ that $\ell$ does not divide $N$, and let $\chi \colon \mathrm{Additive}\,(\mathbb{Z}/N)^\times \to A$ be an additive homomorphism, i.e. a homomorphism from the unit group $(\mathbb{Z}/N)^\times$ written additively. Let [`Ihara.gamma0UnitsChar N`](def/Gamma0UnitsChar.html#L13) be the additivisation of the unit-valued character [`Ihara.gamma0UnitsHom N`](def/Gamma0UnitsChar.html#L5), namely the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ obtained from the monoid homomorphism `CongruenceSubgroup.Gamma0Map N` (reduction of the lower-right entry mod $N$) by passing to units. The assertion is that the homomorphism $\chi \circ \mathrm{gamma0UnitsChar}\,N$ in $\mathrm{Hom}(\mathrm{Additive}\,\Gamma_0(N), A)$ is fixed up to the factor $\ell+1$ by [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285), the endomorphism of $\mathrm{Hom}(\mathrm{Additive}\,\Gamma_0(N), A)$ given by first pulling back along the homomorphism [`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) from [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) (the subgroup of $\Gamma_0(N)$ of elements lying in `heckeUpperSL ℓ`) to $\Gamma_0(N)$ induced by the conjugation `heckeConjMat ℓ`, and then corestricting from that finite-index subgroup back to $\Gamma_0(N)$ by the transfer sum over the coset space. Explicitly, the conclusion is the equality of additive homomorphisms $$\mathrm{heckeOperatorHom}\,(\chi \circ d) = (\ell+1)\cdot(\chi \circ d),$$ where $d$ denotes [`Ihara.gamma0UnitsChar N`](def/Gamma0UnitsChar.html#L13).
--
--   This is the Eisenstein eigenvalue relation: the characters of $\Gamma_0(N)$ that factor through the lower-right-entry character to $(\mathbb{Z}/N)^\times$ are annihilated by $T_\ell - (1+\ell)$ for every prime $\ell \nmid N$. It is used for [`HeckeEis.heckeOperatorHom_eq_of_kernelPair`](thm.html#HeckeEis.heckeOperatorHom_eq_of_kernelPair) and, in the Ihara-lemma route to level raising, for the statement that members of a kernel pair of the level-raising map are Eisenstein modulo three at parabolic level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (χ : Additive (ZMod N)ˣ →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (χ.comp (Ihara.gamma0UnitsChar N)) =
      (ℓ + 1) • χ.comp (Ihara.gamma0UnitsChar N) := by sorry
