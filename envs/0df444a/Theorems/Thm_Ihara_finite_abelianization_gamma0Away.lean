-- Prove2me | Theorems.Thm_Ihara_finite_abelianization_gamma0Away
-- name    : Ihara.finite_abelianization_gamma0Away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/e01c79af-e4dc-52b9-b03e-e1b5e6dd737c
-- title:
--   Finiteness of the abelianisation of Γ₀(N) in SL₂(ℤ[1/q])
-- statement:
--   Let $q$ and $N$ be natural numbers with $q$ prime and $\gcd(N,q)=1$ (so in particular $N\neq 0$, since $\gcd(0,q)=q$). Write `ZAway q` for the localisation of $\mathbb{Z}$ away from $q$, that is the ring $\mathbb{Z}[1/q]$, and let [`Ihara.Gamma0Away N q`](def/Gamma0Away.html#L15) be the subgroup of $\mathrm{SL}(2,\mathbb{Z}[1/q])$ whose underlying set consists of those matrices $g$ for which the image of $N$ in $\mathbb{Z}[1/q]$ divides the lower left entry $g_{1,0}$; the subgroup conditions are the usual computations with the explicit formulae for products and for inverses of $2\times 2$ matrices of determinant one. The theorem asserts that the abelianisation of this subgroup, i.e. its quotient by its commutator subgroup, is a finite group (in the sense of the `Finite` typeclass). Note that the ambient group is the $S$-arithmetic group $\mathrm{SL}(2,\mathbb{Z}[1/q])$, not $\mathrm{SL}(2,\mathbb{Z})$; for $N=1$ the subgroup is all of $\mathrm{SL}(2,\mathbb{Z}[1/q])$.
--
--   This is the finiteness of the abelianisation of the $\Gamma_0(N)$-type $S$-arithmetic subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$, the level-one case going back to Beyl's computation of the Schur multiplier of $\mathrm{SL}_2(\mathbb{Z}/m\mathbb{Z})$. It serves in the development of Ihara's lemma, and is used in [`Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero`](thm.html#Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_finite_abelianization_gamma0Away.lean

import Definitions.Def_Gamma0Away
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ihara.finite_abelianization_gamma0Away {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q) :
    Finite (Abelianization ↥(Ihara.Gamma0Away N q)) := by sorry
