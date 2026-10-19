-- Prove2me | Theorems.Thm_OAI_Saxl_paired_term_projection
-- name    : OAI.Saxl.paired_term_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:43:35.418403+00:00
-- url     : https://prove2.me/theorems/1d7f4608-0873-4b9a-913e-37a24ef02ec3
-- title:
--   Orbit projection of a single paired-sum term selects exactly the complementary pair
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. Words over the pair alphabet $[d]\times[d]$ are identified with words over $[d^2]$; for words $b,b':[n]\to[d]$ write $(b,b')$ for the word $i\mapsto(b_i,b'_i)$. The pair-sum map $\Sigma:W_{n,d^2}\to W_{n,e}$ is the $S_n$-equivariant linear map with $\Sigma(e_{(b,b')})(c)=1$ if $b_i+b'_i=c_i$ for every $i$ (letters read as integers) and $\Sigma(e_{(b,b')})(c)=0$ otherwise; it is the $n$-th tensor power of the letter map $e_{(x,y)}\mapsto e_{x+y}$ (with $e_{x+y}=0$ when $x+y\ge e$). For a word $t:[n]\to[e]$, the orbit projection $\pi_t$ on $W_{n,e}$ keeps the coordinates of the words in the $S_n$-orbit $\{t\circ k:k\in S_n\}$ of $t$ and sets all other coordinates to $0$; it is $S_n$-equivariant.
--
--   Let $H\le S_n$ be a subgroup, let $a:[n]\to[d]$ and $t:[n]\to[e]$ be words and let $\omega\in H$. Assume (i) $t\circ g=t$ for every $g\in H$; (ii) the map $i\mapsto(t_i,a_i)$ is injective; (iii) $a_i+a_{\omega(i)}=t_i$ for every $i\in[n]$. Then for all $g,h\in H$,
--
--   $$
--   \pi_t\Bigl(\Sigma\bigl(e_{(a\circ g,\;a\circ h)}\bigr)\Bigr)=\begin{cases}e_t,& h=\omega g,\\ 0,& h\neq\omega g,\end{cases}
--   $$
--
--   where $\omega g=\omega\circ g$ is the product in $S_n$. Thus, among all terms $e_{(a\circ g,a\circ h)}$ of the tensor square of a signed sum over $H$, only the pairs $(g,\omega g)$ reach the $S_n$-orbit of $t$ under the pair-sum map, and each of them contributes exactly $e_t$. This term-by-term computation underlies the evaluation of the orbit projection of the paired sum of a squared alternating word, which is used in the analysis of the tensor square of the staircase Specht module.
--
--   **Formalization Note** The pair word $(b,b')$ is `mergeWords b b'`, with pairs encoded in `Fin (d*d)` through `finProdFinEquiv`; $\Sigma$ is `pairSumMap n d e`, $\pi_t$ is `orbitProjection t`, and $e_t$ is `Pi.single t 1`. Hypothesis (iii) is an identity of natural numbers between the values of the letters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean#L157-L207

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

theorem OAI.Saxl.paired_term_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by sorry
