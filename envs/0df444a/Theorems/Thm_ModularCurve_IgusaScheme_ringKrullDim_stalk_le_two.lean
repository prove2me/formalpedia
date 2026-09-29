-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_ringKrullDim_stalk_le_two
-- name    : ModularCurve.IgusaScheme.ringKrullDim_stalk_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/7948be1e-5d8a-5f30-81cb-29e49d49c46d
-- title:
--   Stalks of the Igusa scheme have Krull dimension at most two
-- statement:
--   Let $N$ be a natural number that is nonzero and let $\ell$ be a prime. The scheme $\mathtt{IgusaScheme}\,N\,\ell$ is defined as the pushout, in the category of schemes (with ground universe $0$), of the two morphisms $\mathtt{fFin}\,N\,\ell : \mathtt{XMid}\,N\,\ell \to \mathtt{XFin}\,N\,\ell$ and $\mathtt{fInf}\,N\,\ell : \mathtt{XMid}\,N\,\ell \to \mathtt{XInf}\,N\,\ell$, each of which is obtained by applying $\operatorname{Spec}$ to the ring homomorphism underlying an algebra map ($\mathtt{inclFin}$, respectively $\mathtt{inclInf}$); thus it is the scheme got by gluing the two charts $\mathtt{XFin}\,N\,\ell$ and $\mathtt{XInf}\,N\,\ell$ along $\mathtt{XMid}\,N\,\ell$. The assertion is that for every point $x$ of the underlying topological space of this scheme, the Krull dimension of the local ring $\mathcal O_{x}$, the stalk at $x$ of the structure sheaf, is at most $2$ (an inequality of values of $\mathtt{ringKrullDim}$, so in $\mathbb{Z}_{\ge -\infty} \cup \{\infty\}$). No relation between $\ell$ and $N$ is assumed; in particular $\ell$ may divide $N$.
--
--   This is the dimension bound for the two-chart integral model of the modular curve over the localisation of $\mathbb Z$ at $\ell$: its local rings are at most two-dimensional, as expected for a scheme of finite type over a one-dimensional Dedekind base. It is used in the local study of the model, for instance to pass from regularity of a stalk to freeness of localised modules of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_ringKrullDim_stalk_le_two.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.ringKrullDim_stalk_le_two (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (x : ↥(IgusaScheme N ℓ)) : ringKrullDim ((IgusaScheme N ℓ).presheaf.stalk x) ≤ 2 := by sorry
