-- Prove2me | Theorems.Thm_ModPForms_modPMod_le_modPMod_of_dvd
-- name    : ModPForms.modPMod_le_modPMod_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/36d24726-5eed-5eb8-92e8-001f0484cd39
-- title:
--   Mod-p forms of level M embed in level N when M ∣ N
-- statement:
--   Let $M$ and $N$ be natural numbers with $M \mid N$, let $k$ be an integer, and let $F$ be a field. For a natural number $L$, let $\mathrm{modPMod}\ L\ k\ F$ denote the $F$-submodule of $F[[q]]$ spanned by those power series $\varphi$ for which there exist a modular form $f$ of weight $k$ on $\Gamma_0(L)$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ such that, for every $n$, the $n$-th coefficient of the $q$-expansion of $f$ of width $1$ equals the image of $a_n$ in $\mathbb{C}$, and $\varphi$ is the power series whose $n$-th coefficient is the image of $a_n$ in $F$. In other words, the span of the coefficientwise reductions to $F$ of the $q$-expansions at infinity of those weight-$k$ forms on $\Gamma_0(L)$ all of whose Fourier coefficients are rational integers. The assertion is the inclusion of submodules $\mathrm{modPMod}\ M\ k\ F \le \mathrm{modPMod}\ N\ k\ F$.
--
--   This is the level-raising inclusion coming from $\Gamma_0(N) \le \Gamma_0(M)$, i.e. the identity degeneracy (old-form) embedding; the companion embeddings $f(q) \mapsto f(q^d)$ for $d \mid N/M$ are not asserted. It serves to transport low-level mod-$p$ classes to level $N$, and is used in the project's results on membership of explicit power series such as $1$ and theta-type series in the mod-$p$ spaces at a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPMod_le_modPMod_of_dvd.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPMod_le_modPMod_of_dvd (M N : ℕ) (hMN : M ∣ N) (k : ℤ) (F : Type) [Field F] :
    ModPForms.modPMod M k F ≤ ModPForms.modPMod N k F := by sorry
