-- Prove2me | Theorems.Thm_OAI_Erdos3_smoothSource_pair_kernel_reduction
-- name    : OAI.Erdos3.smoothSource_pair_kernel_reduction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:17.745397+00:00
-- url     : https://prove2.me/theorems/eb795236-06b9-44bf-a94a-ad6c53641950
-- title:
--   Reducing a smooth-source pair correlation to residue-cell means through a kernel
-- statement:
--   Let $J,I,A,B,R$ be finite types, $R$ nonempty, and $A,B,R$ with decidable equality. Let $a,S\colon\mathrm{Option}\,J\times I\to\mathbb R$ with $S>0$ and $0<$ `shiftedSmoothProductMass a S` $=\sum_z\prod_c\phi((z_c-a_c)/S_c)$ (sum over integer arrays $z$, $\phi=$ `smoothProbabilityProfile`); write $\Pi=$ `shiftedSmoothProductPMF a S …` for the probability on integer arrays proportional to $\prod_c\phi((z_c-a_c)/S_c)$, and `smoothSourceFiniteWeights a S …` for the same law as finite weights on its (finite) support box. For $\tau\colon J\to\mathbb Z$ write $s_\tau(z)_i=z(\mathrm{none},i)+\sum_j\tau_j\,z(\mathrm{some}\ j,i)$ (`smoothAffineSample`). Let $t,u\colon J\to\mathbb Z$, nonempty finite sets $T,U\subseteq\mathbb Z^I$, and $e,d\colon\mathbb Z^I\to\mathbb R$ vanishing off $T$ and off $U$ respectively. Let $C\colon T\to A$, $D\colon U\to B$, $F\colon T\to R$, $G\colon U\to R$, $k\colon T\times U\to\mathbb R$ and $\mathrm{cell}\colon A\times B\times R\to\mathbb R$, and reals $V,\delta,\gamma,L,K,\varepsilon,\zeta$ with $V>0$, $\delta\ge0$, $L\ge0$, $\varepsilon\ge0$, $\zeta\ge0$. Writing $\mathbb P_T,\mathbb E_T$ for the uniform law on $T$ (`FiniteProbabilityWeights.uniform T`) and likewise for $U$, assume: $\mathbb P_T(F=\varrho)\le K/|R|$ and $\mathbb P_U(G=\varrho)\le K/|R|$ for all $\varrho\in R$; for all $\alpha\in A$, $\varrho\in R$, $|\mathbb E_T[e\,\mathbf 1_{C=\alpha,F=\varrho}]|\le\mathbb P_T(C=\alpha)\,\delta/|R|$ (`finiteCellResidueMean` and `finiteCellWeights`), and similarly $|\mathbb E_U[d\,\mathbf 1_{D=\beta,G=\varrho}]|\le\mathbb P_U(D=\beta)\,\gamma/|R|$; $|\mathrm{cell}|\le L$; for $x\in T$, $y\in U$ with $F(x)\ne G(y)$, the image law of $\Pi$ under `smoothAffinePairRows t u` ($z\mapsto(i\mapsto(s_t(z)_i,s_u(z)_i))$) gives probability $0$ to the point $i\mapsto(x_i,y_i)$ (`affinePairRowsOfLocations (x, y)`); for $F(x)=G(y)$, $|V\cdot(\text{that probability})-|R|\,k(x,y)|\le|R|\,\varepsilon$; and for $F(x)=G(y)$, $|k(x,y)-\mathrm{cell}(C(x),D(y),F(x))|\le\zeta$. Then
--   $$\Big|\mathbb E_{z}\big[e(s_t(z))\,d(s_u(z))\big]\Big|\le\frac{|T|\,|U|}V\Big(L\delta\gamma+(\varepsilon+\zeta)\frac K2\big(\mathbb E_T[e^2]+\mathbb E_U[d^2]\big)\Big),$$
--   the mean on the left taken under `smoothSourceFiniteWeights a S hS hZ`.
--
--   Lean: `OAI.Erdos3.smoothSource_pair_kernel_reduction` in `lean/OAI/Combinatorics/Progressions/Estimates/SmoothPairErrorLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B089` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmoothPairErrorLogBounds.lean#L102

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B089

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSource_pair_kernel_reduction {J I A B R : Type*}
    [Fintype J] [Fintype I] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (C : T → A) (D : U → B) (F : T → R) (G : U → R)
    (k : T → U → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) C F (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) C).weight c * delta / Fintype.card R)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) D G (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) D).weight c * gamma / Fintype.card R)
    (hcell : ∀ c c' r, |cell c c' r| ≤ L)
    (hoff : ∀ x : T, ∀ y : U, F x ≠ G y →
      ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal = 0)
    (hpoint : ∀ x : T, ∀ y : U, F x = G y →
      |V * ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal -
          (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  sorry

end Erdos3
end
end OAI
