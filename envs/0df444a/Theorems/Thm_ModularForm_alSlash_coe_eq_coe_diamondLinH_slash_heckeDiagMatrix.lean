-- Prove2me | Theorems.Thm_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
-- name    : ModularForm.alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/7b616087-c209-58c3-bd54-e610ef16de8e
-- title:
--   Atkin–Lehner slash as a diamond followed by diag(p,1)
-- statement:
--   Fix natural numbers $M$ and $p$ with $M \neq 0$, with $p$ prime, and an Atkin–Lehner datum $W$ at $(M,p)$: that is, a natural number $R = W.R$ (assumed nonzero) with $M = pR$ together with integers $a, b$ satisfying $pa - Rb = 1$. Let $H' \le (\mathbb{Z}/R)^{\times}$ be a subgroup, $k \in \mathbb{Z}$, and let $G$ be a cusp form of weight $k$ for the congruence subgroup [`CohCarrier.GammaH W.R H'`](def/CohCarrier_Level.html#L133), the image in $SL_2(\mathbb{Z})$ of those elements of $\Gamma_0(R)$ whose associated unit in $(\mathbb{Z}/R)^{\times}$ — the class of the lower right entry — lies in $H'$. Let $d_0 \in (\mathbb{Z}/R)^{\times}$ be a unit whose image in $\mathbb{Z}/R$ is the class of $p$. The conclusion is an identity of functions $\mathbb{H} \to \mathbb{C}$: the weight-$k$ slash of $G$ by $W.alGL$, the element of $GL_2(\mathbb{R})$ given by the integral matrix `W.mat` of the datum (of determinant $p$), equals the weight-$k$ slash of $\langle d_0 \rangle G$ by [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21), i.e. by $\mathrm{diag}(p,1)$. Here $\langle d_0 \rangle$ is [`CuspForm.diamondLinH k d₀`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the $\mathbb{C}$-linear endomorphism sending $f$ to $f \mid_k \gamma$ for a fixed $SL_2(\mathbb{Z})$-lift $\gamma$ of $d_0$, provided the vanishing-at-cusps condition [`CuspForm.StableD`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72) holds for $(R, H', k)$, and the zero map otherwise. The primality of $p$ enters only through $p \neq 0$.
--
--   This is the standard factorisation of the Atkin–Lehner type operator attached to the pair $(M,p)$, acting on forms of the lower level $R = M/p$, as a diamond operator followed by $\tau \mapsto p\tau$ (up to the weight-$k$ slash normalisation). It is used to compute the $q$-expansion coefficients on the $W$-side of level-lowered forms, in the statements about integrality of two-cusp data and the $U_p$- and $H$-Hecke stability of such data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p) [NeZero W.R]
    (H' : Subgroup (ZMod W.R)ˣ) (k : ℤ) (G : CuspForm (CohCarrier.GammaH W.R H') k)
    (d₀ : (ZMod W.R)ˣ) (hd₀ : (d₀ : ZMod W.R) = (p : ZMod W.R)) :
    ModularForm.alSlash W k ⇑G = (⇑(CuspForm.diamondLinH k d₀ G)) ∣[k] ModularForm.heckeDiagMatrix p := by sorry
