-- Prove2me | Theorems.Thm_ModPForms_modPMod_eq_span_map_modPMod_zmod
-- name    : ModPForms.modPMod_eq_span_map_modPMod_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a3c31b5e-df99-56f3-a668-87ae45aab6c8
-- title:
--   Mod p modular forms base change from 𝔽ₚ
-- statement:
--   Let $p$ be a prime, $N$ a natural number, $k$ an integer and $F$ a field of characteristic $p$. For a field $E$ of characteristic $p$, [`ModPForms.modPMod N k E`](def/CuspForm_ModPForms.html#L12) denotes the $E$-submodule of $E[[q]]$ spanned by those power series $\varphi$ for which there exist a modular form $f$ of weight $k$ on $\Gamma_0(N)$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ of integers with $\mathrm{qCoeff}\, f\, n = a_n$ in $\mathbb{C}$ for every $n$ — where $\mathrm{qCoeff}\, f\, n$ is the $n$-th coefficient of the $q$-expansion of $f$ of width $1$ — and $\varphi = \sum_n \overline{a_n}\, q^n$, the coefficients being the images of the $a_n$ under the canonical ring map $\mathbb{Z} \to E$. The assertion is that [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) coincides with the $F$-span of the image of the set underlying [`ModPForms.modPMod N k (ZMod p)`](def/CuspForm_ModPForms.html#L12) under the coefficientwise map $\mathbb{F}_p[[q]] \to F[[q]]$ induced by the canonical ring homomorphism $\mathbb{F}_p \to F$.
--
--   This is the base-change statement for the spaces of mod $p$ $q$-expansions used in the project: every such space over a field of characteristic $p$ is generated over that field by the corresponding space over the prime field. It is used in [`ModPForms.mem_modPMod_sub_of_qP_mul_mem`](thm.html#ModPForms.mem_modPMod_sub_of_qP_mul_mem), and it allows inclusions between these spans to be transferred from $\mathbb{F}_p$ to an arbitrary field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPMod_eq_span_map_modPMod_zmod.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPMod_eq_span_map_modPMod_zmod (p : ℕ) [Fact p.Prime] (N : ℕ) (k : ℤ) (F : Type) [Field F] [CharP F p] :
    ModPForms.modPMod N k F =
      Submodule.span F (PowerSeries.map (ZMod.castHom (dvd_refl p) F) ''
        (ModPForms.modPMod N k (ZMod p) : Set (PowerSeries (ZMod p)))) := by sorry
