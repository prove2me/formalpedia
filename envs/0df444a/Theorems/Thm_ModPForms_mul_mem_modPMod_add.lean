-- Prove2me | Theorems.Thm_ModPForms_mul_mem_modPMod_add
-- name    : ModPForms.mul_mem_modPMod_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/5453ea21-da0e-581e-b75e-deee85d9663f
-- title:
--   Weights add under multiplication of reduced modular forms
-- statement:
--   Fix a natural number $N$, integers $a$ and $b$, and a field $F$. For an integer $k$, let $\widetilde M_k(N;F)$ denote [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12): the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \overline{c(n)}\,q^n$, where $c : \mathbb{N} \to \mathbb{Z}$ is an integer sequence, $\overline{\phantom{c}}$ denotes the image of an integer in $F$, and there exists a modular form $f$ of weight $k$ for $\Gamma_0(N)$ all of whose $q$-expansion coefficients (the coefficients of `qExpansion 1 f`, the expansion taken with period $1$) satisfy $\mathrm{qCoeff}(f)(n) = c(n)$ in $\mathbb{C}$. The theorem asserts: if $\varphi, \psi \in F[[q]]$ satisfy $\varphi \in \widetilde M_a(N;F)$ and $\psi \in \widetilde M_b(N;F)$, then the product $\varphi\psi$ lies in $\widetilde M_{a+b}(N;F)$. No assumption is made on the characteristic of $F$ or on $N$.
--
--   This is the multiplicativity of the graded structure on the spaces of reductions of integral modular forms on $\Gamma_0(N)$: the family $(\widetilde M_k(N;F))_{k \in \mathbb{Z}}$ is a graded subring of $F[[q]]$. It is used in the study of the filtration of such spaces, being cited by [`ModPForms.modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two) and by [`ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two`](thm.html#ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mul_mem_modPMod_add.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mul_mem_modPMod_add (N : ℕ) (a b : ℤ) (F : Type) [Field F]
    (φ ψ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N a F) (hψ : ψ ∈ ModPForms.modPMod N b F) :
    φ * ψ ∈ ModPForms.modPMod N (a + b) F := by sorry
