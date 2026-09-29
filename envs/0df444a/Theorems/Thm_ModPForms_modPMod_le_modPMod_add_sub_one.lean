-- Prove2me | Theorems.Thm_ModPForms_modPMod_le_modPMod_add_sub_one
-- name    : ModPForms.modPMod_le_modPMod_add_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a0bec93e-6d47-5596-b61c-3cd8ef9c7b77
-- title:
--   Mod p forms of weight k lie in weight k+p-1
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N'$ be a nonzero natural number, let $k$ be an integer, and let $F$ be a field of characteristic $p$. For a level $N'$ and a weight $k$, write $\mathrm{modPMod}\,N'\,k\,F$ for the $F$-submodule of $F[[q]]$ spanned by those formal power series $\varphi$ for which there exist a modular form $f$ of weight $k$ for $\Gamma_0(N')$ and a sequence $a \colon \mathbb{N} \to \mathbb{Z}$ of integers such that the $n$-th coefficient of the $q$-expansion of $f$ (taken with respect to the period $1$) equals $a_n$ in $\mathbb{C}$ for every $n$, and $\varphi$ is the power series whose $n$-th coefficient is the image of $a_n$ in $F$. The theorem asserts the inclusion of submodules of $F[[q]]$ $$\mathrm{modPMod}\,N'\,k\,F \le \mathrm{modPMod}\,N'\,(k + (p-1))\,F,$$ that is, every mod $p$ form of weight $k$ and level $N'$ is also a mod $p$ form of weight $k + p - 1$ and level $N'$, the underlying power series being unchanged.
--
--   This is the standard weight shift for mod $p$ modular forms: multiplication by a weight $p-1$ form congruent to $1$ modulo $p$ embeds the mod $p$ forms of weight $k$ into those of weight $k+p-1$, so that the spaces of mod $p$ forms of a fixed level form an increasing filtration along residue classes of the weight modulo $p-1$. It is used in [`ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero`](thm.html#ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero), where weights are normalised upwards before passing to weight $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPMod_le_modPMod_add_sub_one.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPMod_le_modPMod_add_sub_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] :
    modPMod N' k F ≤ modPMod N' (k + ((p : ℤ) - 1)) F := by sorry
