-- Prove2me | Theorems.Thm_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
-- name    : HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/27ab7c2c-24ed-520f-976e-c91aa19993d8
-- title:
--   Diagonal element intertwines Hecke conjugation with reduction mod q
-- statement:
--   Fix natural numbers $N$ and $q$ with $q$ prime, a commutative ring $K$, and a representation $W$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ (the unit group of $2\times 2$ matrices over $\mathbb{Z}/q$) on a $K$-module $W_c$. Let $\mathrm{red} \colon \Gamma_0(N) \to \mathrm{GL}_2(\mathbb{Z}/q)$ be a group homomorphism which is assumed to be the composite of the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$, entrywise reduction along $\mathbb{Z} \to \mathbb{Z}/q$, and the passage from $\mathrm{SL}_2$ to $\mathrm{GL}_2$. Let $\ell$ be a nonzero natural number whose residue $\ell \bmod q$ is nonzero, so that $\ell$ defines a unit of $\mathbb{Z}/q$, and write $d_\ell$ for the element $\begin{pmatrix} \ell & 0 \\ 0 & 1\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{Z}/q)$, namely [`CuspidalType.diagElem`](def/CuspidalType_IsCuspidalOfType.html#L35) applied to that unit. Let $u$ be an element of the subgroup of $\Gamma_0(N)$ consisting of those $\begin{pmatrix} a & b \\ c & e\end{pmatrix}$ with $\ell \mid b$, and let $\mathrm{heckeConj}(u) \in \Gamma_0(N)$ be $\begin{pmatrix} a & b/\ell \\ c\ell & e\end{pmatrix}$. The conclusion is an equality of $K$-linear endomorphisms of $W_c$: $W(d_\ell) \circ W(\mathrm{red}(\mathrm{heckeConj}(u))) = W(\mathrm{red}(u)) \circ W(d_\ell)$.
--
--   This records the conjugation relation $d_\ell \gamma' = \gamma d_\ell$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ between an element $\gamma$ of $\Gamma_0(N)$ with upper-right entry divisible by $\ell$ and its $\ell$-conjugate $\gamma'$, transported to any representation $W$ of $\mathrm{GL}_2(\mathbb{Z}/q)$. It is used in the analysis of Hecke eigensystems on degree-one cohomology, in particular in the results on cuspidal type and on Steinberg quotients that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
    (N q : ℕ) [Fact q.Prime] (K : Type) [CommRing K]
    {Wc : Type} [AddCommGroup Wc] [Module K Wc] (W : Representation K (CuspidalType.GL2 q) Wc)
    (red : CongruenceSubgroup.Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (CongruenceSubgroup.Gamma0 N).subtype)
    (ℓ : ℕ) [NeZero ℓ] (h : (ℓ : ZMod q) ≠ 0) (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) ∘ₗ (W.comp red) (HeckeEis.heckeConj N ℓ u) =
      (W.comp red) (u : CongruenceSubgroup.Gamma0 N) ∘ₗ W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) := by sorry
