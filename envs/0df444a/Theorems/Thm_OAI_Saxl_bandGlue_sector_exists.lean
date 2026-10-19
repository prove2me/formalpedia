-- Prove2me | Theorems.Thm_OAI_Saxl_bandGlue_sector_exists
-- name    : OAI.Saxl.bandGlue_sector_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:21:04.134446+00:00
-- url     : https://prove2.me/theorems/1d3fe19b-37a4-4874-986d-f729be8e32cc
-- title:
--   Gluing a colored left-block map with band intertwiners gives a nonzero sector-supported equivariant map
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. For $m,d\in\mathbb{N}$ let $W_{m,d}$ be the space of functions from words $w:[m]\to[d]$ to $\mathbb{C}$, on which $S_m$ acts by $(g\cdot x)(w)=x(w\circ g)$; thus the indicator $\delta_w$ of a word is sent to $\delta_{w\circ g^{-1}}$. For $x\in W_{m,d}$ let $\langle x\rangle\subseteq W_{m,d}$ be the cyclic subrepresentation spanned by $\{g\cdot x:g\in S_m\}$. A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ ($i$ the row, $j$ the column) that is closed under moving up or to the left; $|\lambda|$ is its number of cells and $\ell(\lambda)$ its number of rows. A tableau of shape $\lambda$ on $[m]$ is a bijection $t:[m]\to\lambda$ (so $|\lambda|=m$). Its row word $r_t:[m]\to[\ell(\lambda)]$ sends $k$ to the row of $t(k)$; its column group $C_t\le S_m$ consists of the permutations $g$ such that $t(g(k))$ and $t(k)$ lie in the same column for every $k$; its polytabloid is $p_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in W_{m,\ell(\lambda)}$; and its Specht module $S^t\subseteq W_{m,\ell(\lambda)}$ is the $S_m$-invariant subspace spanned by $\{g\cdot p_t: g\in S_m\}$, with the restricted action.
--
--   Fix $n,a,b,k,d\in\mathbb{N}$. Let $e:[n]\to[a]\sqcup[b]$ be a bijection; it splits the $n$ positions into $a$ *left* positions $e^{-1}([a])$ and $b$ *right* positions $e^{-1}([b])$. For $h\in S_a$ and $q\in S_b$ let $h\oplus q=e^{-1}\circ(h\sqcup q)\circ e\in S_n$ be the permutation that acts as $h$ on the left positions and as $q$ on the right positions. For a word $w:[n]\to[d]$ let $w_L:[a]\to[d]$ and $w_R:[b]\to[d]$ be its restrictions to the left and right positions read through $e$, and for $x\in W_{a,d}$, $y\in W_{b,d}$ let $x\otimes_e y\in W_{n,d}$ be given by $(x\otimes_e y)(w)=x(w_L)\,y(w_R)$. Let $\rho$ be a representation of $S_n$ on a complex vector space $X$, let $A\subseteq[d]$ be a set of letters, and assume:
--
--   1. $v\in W_{a,d}$ vanishes on every word that uses a letter outside $A$, and $u\in W_{b,d}$ vanishes on every word that uses a letter in $A$;
--   2. for every Young diagram $\mu$ with $b$ cells and at most $k$ rows and every tableau $t:[b]\to\mu$ there is a nonzero $S_b$-equivariant linear map $S^t\to\langle u\rangle$;
--   3. $T$ is a nonzero linear map from $X$ to the space of functions from colorings $c:[b]\to[k]$ to $W_{a,d}$, with $T(x)(c)\in\langle v\rangle$ for all $x$ and $c$, which is equivariant in the sense of the identity below.
--
--   $$
--   T\bigl(\rho(h\oplus q)\,x\bigr)(c)=h\cdot T(x)(c\circ q)\qquad(h\in S_a,\ q\in S_b,\ x\in X,\ c:[b]\to[k]).
--   $$
--
--   Then there is a nonzero linear map $f:X\to W_{n,d}$ that is equivariant for the Young subgroup,
--   $$
--   f\bigl(\rho(h\oplus q)\,x\bigr)=(h\oplus q)\cdot f(x)\qquad(h\in S_a,\ q\in S_b,\ x\in X),
--   $$
--   and such that for every $x\in X$:
--
--   1. $f(x)\in\langle v\otimes_e u\rangle$;
--   2. $f(x)(w)=0$ for every word $w:[n]\to[d]$ outside the sector of $A$, that is, unless for every position $i\in[n]$ the letter $w(i)$ lies in $A$ exactly when $i$ is a left position.
--
--   This is the gluing step of the support-transfer argument for horizontal strips: a nonzero colored family of maps into the cyclic module $\langle v\rangle$ on the left block is combined with band intertwiners into $\langle u\rangle$ on the right block, producing a nonzero $S_a\times S_b$-equivariant map into $\langle v\otimes_e u\rangle$ supported on a single coordinate sector, ready for averaging over the sector stabilizer.
--
--   **Formalization Note** $\langle x\rangle$ is `cyclic (wordRep m d) x`, $x\otimes_e y$ is `positionProduct e x y`, $h\oplus q$ is `sumPerm e h q` and $S^t$ is `spechtRep t`. The hypotheses on $v$ and $u$ are membership in `alphabetSub a d A` and `alphabetSub b d (fun z => ¬A z)`, the sector condition is membership in `coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)`, and "at most $k$ rows" is `μ.colLen 0 ≤ k`; a tableau `Tableau b μ` exists only when $|\mu|=b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandGlue.lean#L170-L212

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.bandGlue_sector_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hvA : v ∈ alphabetSub a d A)
    (huA : u ∈ alphabetSub b d (fun z => ¬A z))
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) ∧
      (∀ x, f x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)) := by sorry
