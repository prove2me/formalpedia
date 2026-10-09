-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_exists_nonexceptional_residue
-- name    : OAI.SevenEighths.ProbeGramCommon.exists_nonexceptional_residue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:46.712124+00:00
-- url     : https://prove2.me/theorems/c1553a0c-5bb2-4739-9179-cee0b70f05fb
-- title:
--   The joint extension at a nonexceptional prime has mean zero
-- statement:
--   Let $S$ be a finite set of maximal ideals, $\sigma$, $C,k\ne0$ with $k=u\lambda^a2^br$ ($u$ a unit, $\lambda=$`goodLambda`, $r$ `Supported`), $(C)=\prod_iP_i^{c_i}$ with maximal $P_i$ avoiding $\lambda$ and $c_i\ge1$, and a maximal ideal $p\ne0$ avoiding $\lambda$, of odd residue characteristic, not dividing `jointFixedModulus S` nor $\prod P_i$, whose multiplicity in $(r)$ is not divisible by 6. Then there is a nonzero ideal $M$ with $N(M)\le N(\texttt{jointFixedModulus}\,S)N((C))N((k))$ such that for every $d$ there is $A:(\mathcal O/M)^2\to\mathbb C$ with $A(\bar n_1,\bar n_2)=$`jointExtension S hS σ C k u a b r hr P hg c (d n₁) (d n₂)` for all $n_1,n_2$, $|A|\le N((C))$ and $\sum_{x,y}A(x,y)=0$.
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.exists_nonexceptional_residue` in `lean/OAI/NumberTheory/DirichletL/Detector/GramResidue.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
