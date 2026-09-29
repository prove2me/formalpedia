-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod
-- name    : ModPForms.mem_modPMod_of_mul_mem_of_forall_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/16668981-a10b-56cd-9d06-5adc45e821a6
-- title:
--   Descent of filtration implications from mathbb Fₚ to characteristic p fields
-- statement:
--   Let $p$ be a prime, $N$ a natural number, $k,k',k''$ integers and $F$ a field of characteristic $p$. For a field $F'$ of characteristic $p$ write $\mathrm{modPMod}\,N\,k\,F'$ for the $F'$-submodule of $F'[[q]]$ spanned by those power series of the form $\mathrm{PowerSeries.mk}\,(n \mapsto (a_n : F'))$ where $a : \mathbb N \to \mathbb Z$ is a sequence of integers and there is a modular form $f$ of weight $k$ on $\Gamma_0(N)$ whose $q$-expansion coefficients (the coefficients of the $q$-expansion of width $1$, `qCoeff`) satisfy $\mathrm{qCoeff}\,f\,n = a_n$ in $\mathbb C$ for every $n$; that is, the span of the coefficientwise reductions of $q$-expansions at infinity of weight-$k$ forms on $\Gamma_0(N)$ having integral Fourier coefficients. Let $P \in \mathbb F_p[[q]]$ and assume the implication over the prime field: for every $\psi \in \mathbb F_p[[q]]$, if $\psi \in \mathrm{modPMod}\,N\,k\,\mathbb F_p$ and $P\psi \in \mathrm{modPMod}\,N\,k'\,\mathbb F_p$, then $\psi \in \mathrm{modPMod}\,N\,k''\,\mathbb F_p$. Then for every $\varphi \in F[[q]]$ with $\varphi \in \mathrm{modPMod}\,N\,k\,F$ and with the product of the coefficientwise image of $P$ under the canonical map $\mathbb F_p \to F$ by $\varphi$ lying in $\mathrm{modPMod}\,N\,k'\,F$, one has $\varphi \in \mathrm{modPMod}\,N\,k''\,F$.
--
--   This is the descent step which allows statements of the shape 'multiplication by a fixed power series with coefficients in $\mathbb F_p$ forces membership in another weight' to be checked over the prime field only and then used over an arbitrary field of characteristic $p$, the coefficients of $P$ being rational over $\mathbb F_p$ while $\varphi$ is not. It is used by [`ModPForms.mem_modPMod_sub_of_qP_mul_mem`](thm.html#ModPForms.mem_modPMod_sub_of_qP_mul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mem_modPMod_of_mul_mem_of_forall_zmod (p : ℕ) [Fact p.Prime] (N : ℕ) (k k' k'' : ℤ) (F : Type) [Field F] [CharP F p]
    (P : PowerSeries (ZMod p))
    (h : ∀ ψ : PowerSeries (ZMod p), ψ ∈ ModPForms.modPMod N k (ZMod p) →
      P * ψ ∈ ModPForms.modPMod N k' (ZMod p) → ψ ∈ ModPForms.modPMod N k'' (ZMod p))
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F)
    (hP : PowerSeries.map (ZMod.castHom (dvd_refl p) F) P * φ ∈ ModPForms.modPMod N k' F) :
    φ ∈ ModPForms.modPMod N k'' F := by sorry
