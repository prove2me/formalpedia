-- Prove2me | Theorems.Thm_OAI_Saxl_repeated_alt_projection
-- name    : OAI.Saxl.repeated_alt_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:44:56.039561+00:00
-- url     : https://prove2.me/theorems/92f3d076-4fe0-4db2-ab61-fa5d2b3121dc
-- title:
--   Orbit projection of the paired sum of a squared signed orbit sum
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. Words over the pair alphabet $[d]\times[d]$ are identified with words over $[d^2]$; for words $b,b':[n]\to[d]$ write $(b,b')$ for the word $i\mapsto(b_i,b'_i)$. The pair-sum map $\Sigma:W_{n,d^2}\to W_{n,e}$ is the $S_n$-equivariant linear map with $\Sigma(e_{(b,b')})(c)=1$ if $b_i+b'_i=c_i$ for every $i$ (letters read as integers) and $\Sigma(e_{(b,b')})(c)=0$ otherwise; it is the $n$-th tensor power of the letter map $e_{(x,y)}\mapsto e_{x+y}$ (with $e_{x+y}=0$ when $x+y\ge e$). For a word $t:[n]\to[e]$, the orbit projection $\pi_t$ on $W_{n,e}$ keeps the coordinates of the words in the $S_n$-orbit $\{t\circ k:k\in S_n\}$ of $t$ and sets all other coordinates to $0$; it is $S_n$-equivariant. Finally, $W_{n,d}\otimes W_{n,d}$ is identified with $W_{n,d^2}$ via $e_b\otimes e_{b'}\mapsto e_{(b,b')}$, and for a subgroup $H\le S_n$ and a word $a:[n]\to[d]$ the signed orbit sum is $\mathrm{alt}_H(a)=\sum_{g\in H}\operatorname{sgn}(g)\,g\cdot e_a\in W_{n,d}$.
--
--   Let $H\le S_n$ be a subgroup, let $a:[n]\to[d]$ and $t:[n]\to[e]$ be words and let $\omega\in H$. Assume (i) $t\circ g=t$ for every $g\in H$; (ii) the map $i\mapsto(t_i,a_i)$ is injective; (iii) $a_i+a_{\omega(i)}=t_i$ for every $i\in[n]$. Then
--
--   $$
--   \pi_t\Bigl(\Sigma\bigl(\mathrm{alt}_H(a)\otimes\mathrm{alt}_H(a)\bigr)\Bigr)=|H|\,\operatorname{sgn}(\omega)\,e_t .
--   $$
--
--   In particular the left-hand side is nonzero. When $H$ is the column group of a tableau and $a$ is its row word, $\mathrm{alt}_H(a)$ is the polytabloid of that tableau, and the identity computes the component in the $S_n$-orbit of $t$ of the pair-sum image of the tensor square of the polytabloid. This is how a specific word orbit is shown to be reached from the tensor square of the staircase polytabloid.
--
--   **Formalization Note** $\mathrm{alt}_H(a)$ is `altWord H a`, the identification of the tensor square is `wordTensor n d d`, $|H|$ is `Nat.card H`, and the sign is the complex-valued character `signC`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean#L209-L229

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
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.repeated_alt_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by sorry
