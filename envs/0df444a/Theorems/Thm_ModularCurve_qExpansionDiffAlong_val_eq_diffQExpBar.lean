-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExpBar
-- name    : ModularCurve.qExpansionDiffAlong_val_eq_diffQExpBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/ca1d69fc-5845-5292-a3da-da0c0d63ada5
-- title:
--   The two q-expansion maps on differentials agree
-- statement:
--   Let $N$ be a nonzero natural number and write $\bar F_N =$ `modularFunctionFieldBar N` for the intermediate field of $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$ obtained by base change along the coefficientwise embedding: it is generated over $\overline{\mathbb{Q}}$ by the image under `coeffEmb` of the subfield `modularFunctionFieldFull N` of $\mathbb{Q}((q))$, the latter being the field generated over $\mathbb{Q}$ by the Laurent series in `divisorExpansions N`. Let $\omega$ be an element of the module of Kähler differentials $\Omega[\bar F_N / \overline{\mathbb{Q}}]$. The assertion is that the two maps on differentials agree at $\omega$: on one side, `qExpansionDiffAlong` applied to the inclusion $\bar F_N \hookrightarrow \overline{\mathbb{Q}}((q))$, i.e. (by definition) a chosen $\overline{\mathbb{Q}}$-linear map $\varphi : \Omega[\bar F_N/\overline{\mathbb{Q}}] \to \overline{\mathbb{Q}}((q))$ satisfying $\varphi(D x) = \mathrm{thetaL}(x)$ for all $x \in \bar F_N$ and $\varphi(f \cdot \omega) = f\,\varphi(\omega)$, if such a map exists, and the zero map otherwise; on the other side, `diffQExpBar N`, the $\bar F_N$-linear lift along the universal derivation $D$ of the Euler derivation `qEulerOn` $= q\,\mathrm{d}/\mathrm{d}q$ of $\bar F_N$.
--
--   This is the compatibility statement identifying two packagings of the Laurent expansion of a differential of the level-$N$ modular function field at the cusp: the lift of the Euler derivation $q\,\mathrm{d}/\mathrm{d}q$ along the universal derivation, and the map characterised axiomatically relative to an embedding into Laurent series. It is the link between the two vocabularies, used where differentials with prescribed $q$-expansions are compared with rational curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExpBar.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExpBar (N : ℕ) [NeZero N]
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) :
    qExpansionDiffAlong (modularFunctionFieldBar N).val ω = diffQExpBar N ω := by sorry
