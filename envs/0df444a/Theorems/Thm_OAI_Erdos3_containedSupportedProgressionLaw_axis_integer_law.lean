-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_axis_integer_law
-- name    : OAI.Erdos3.containedSupportedProgressionLaw_axis_integer_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:43:23.602744+00:00
-- url     : https://prove2.me/theorems/4acf55b6-25c4-4e46-91ed-3e1726256782
-- title:
--   Axis marginal of the contained supported progression law is a product of affine images
-- statement:
--   Section variables: finite types $D$ and $\alpha$ with decidable equality; for each $d\in D$ a finite type $B_d$ with decidable equality and a natural number $h_d$; the index type $\mathcal J=$ `PrincipalTupleIndex B h` of triples $(d,b,v)$ with $b\in B_d$, $v\in\mathrm{Fin}\,h_d$; functions $L,H,\mathrm{step}\colon\mathcal J\to\mathbb N$ and $c\colon\mathcal J\to\mathbb Z$ with $L_j>0$, $H_j>0$, and (`hsubset`) $\{c_j+\mathrm{step}_j\,n:0\le n<H_j\}\subseteq\{0,\dots,L_j-1\}$ for every $j$ (`integerProgressionSupport`); a natural number $q$ and $r\colon\mathcal J\to(\mathrm{Option}\,\alpha\to\mathbb Z/q)$; and (`hcell`) positivity of the mass, under `principalTupleWeights B h H hH`, of the set of tuples $y$ whose residues mod $q$ (`principalResidueLabel q y`) equal $r$. Here `principalTupleWeights B h H hH` is the product over $j\in\mathcal J$ of `integerScalarCubeWeights α (H j)` (the uniform law on the integer scalar cube of side $H_j$ inside `IntegerScalarCubeBox α (H j)`), and `containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell` is the push-forward of that product law, conditioned on the residue cell $r$, under the map `containedProgressionTupleMap`, which sends each component $y_j$ to the cube point of side $L_j$ obtained from $i\mapsto c_j\mathbf 1[i=\mathrm{none}]+\mathrm{step}_j\,y_j(i)$. Let $q>0$, $a\in D$, and assume $(|\alpha|+1)\,q\le H_{(a,b,v)}$ for all $b,v$. Then the law of the $a$-block $\big((b,v,i)\mapsto y_{(a,b,v)}(i)\in\mathbb Z\big)$ when $y$ is drawn from `containedSupportedProgressionLaw …` equals `dependentProductPMF` over $b\in B_a$ (the independent product of PMFs) of the image of `dependentProductPMF` over $v\in\mathrm{Fin}\,h_a$ of the laws `(principalSupportedAxisSources B h H hH q hq r a hsize b v).source` under the map $y\mapsto\big(v,i\mapsto c_{(a,b,v)}\mathbf 1[i=\mathrm{none}]+\mathrm{step}_{(a,b,v)}\,y_v(i)\big)$. Here `principalSupportedAxisSources … b v` is the `NormalizedScalarCubeSource α` `normalizedUniformCubeSource` of length $H_{(a,b,v)}$ with all moduli equal to $q$ and residues $r_{(a,b,v)}$, and `.source` is its probability law on `IntegerScalarCubeBox α (H (a,b,v))`.
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionLaw_axis_integer_law` in `lean/OAI/Combinatorics/Progressions/Probability/ContainedSupportedProgressionJetLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B097` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/ContainedSupportedProgressionJetLaw.lean#L40

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B097

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

theorem containedSupportedProgressionLaw_axis_integer_law (hq : 0 < q) (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
      (fun y (b : B a) (v : Fin (h a)) i => (y ⟨a,b,v⟩ i : ℤ)) =
      dependentProductPMF (fun b => (dependentProductPMF (fun v =>
        (principalSupportedAxisSources B h H hH q hq r a hsize b v).source.toPMF)).map
          (fun y v i => (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y v i : ℤ))) := by
  sorry

end Erdos3
end
end OAI
