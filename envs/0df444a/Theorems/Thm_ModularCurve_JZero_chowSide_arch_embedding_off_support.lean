-- Prove2me | Theorems.Thm_ModularCurve_JZero_chowSide_arch_embedding_off_support
-- name    : ModularCurve.JZero.chowSide_arch_embedding_off_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/39395ffb-d518-543e-a7b6-58375c3773ce
-- title:
--   Chow-side archimedean comparison off the support of B
-- statement:
--   Let $N\ge 1$, let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series, and let $E$ be `embDivisor N`, the divisor `embDegree N` times the cusp `cuspInftyBar N`. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $L(E)=\{f : v(f)\le \exp(E(v))\ \forall v\}$. The assertion is the existence of a real constant $c$, depending only on $N$ and $s$, such that for every ring homomorphism $\sigma : \overline{\mathbb Q}\to\mathbb C$, every $k\in\mathbb N$, every $u\ne 0$ in $L(kE)$, and every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+kE(w)$ for all places $w$, the following holds under the hypothesis that `ChowReciprocity s (embDivisor N) k' u' B'` — the two-sided identity $F_{B'}(a)\,F_{Z_c}(b)^{k'}F_{Z_a}(c)^{k'}\,\mathrm{secProd}(k',u',Z_b) = F_{B'}(b)\,F_{Z_c}(a)^{k'}F_{Z_b}(c)^{k'}\,\mathrm{secProd}(k',u',Z_a)$ for all linear sections $a,b,c$ with nonvanishing $\mathrm{linSec}$, their cycles $Z_a,Z_b,Z_c$ given by $\mathrm{div}(\mathrm{linSec})+E$, and the disjointness condition $(Z_a(w)=0\wedge Z_b(w)=0)\vee(B'(w)=0\wedge Z_c(w)=0)$ at every $w$ — holds for all $k'$, all $u'\ne0$ in $L(k'E)$ and all $B'=\mathrm{div}(u')+k'E$: there is a real number $m$ (allowed to depend on $\sigma,k,u,B$ but not on the place) such that for every place $v$ of $\bar F_N$ over $\overline{\mathbb Q}$ with $B(v)=0$, $$\Bigl|\,\mathrm{chowSide}(|\sigma(\cdot)|,s,B,v) - \bigl(k\log \sup_i |\sigma(\mathrm{evalVec}\,s\,v\,i)| - \log|\sigma(\mathrm{secVal}\,s\,v\,k\,u)| - m\bigr)\Bigr|\le c\,k,$$ where $\mathrm{evalVec}\,s\,w$ is the pivot-normalised coordinate vector $w \mapsto (w(s_i/s_{\mathrm{piv}}))_i$, $\mathrm{secVal}\,s\,v\,k\,u = v(u\cdot s_{\mathrm{piv}}^{-k})$, and $\mathrm{chowSide}$ is $\sum_w B(w)\log\sup_i|\sigma(\mathrm{evalVec}\,s\,w\,i)|$ minus the logarithm of the supremum of $|\sigma(F_B(a))|/(\sup_i|\sigma(a_i)|)^{\sum_w B(w)^+}$ over nonzero $a$ with $\sum_i \mathrm{evalVec}\,s\,v\,i\cdot a_i=0$, with $F_B = \prod_w(\sum_i \mathrm{evalVec}\,s\,w\,i\,X_i)^{B(w)^+}$.
--
--   This is the off-support line of the archimedean comparison between the Chow side of the section cycle $B=\mathrm{div}(u)+kE$ and the naive expression $k\log\|x_v\|_\sigma-\log|\sigma(u(v))|$, along the projective embedding of the modular curve of level $N$ furnished by $L(E)$; the error is $O(k)$ with a constant uniform in $\sigma$, $k$, $u$ and the place. It is combined with the corresponding statement at the base cusp in [`ModularCurve.JZero.chowSide_arch_embedding`](thm.html#ModularCurve.JZero.chowSide_arch_embedding), which assembles the two lines with a single constant $m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chowSide_arch_embedding_off_support.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chowSide_arch_embedding_off_support (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      (∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
          (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
          (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
          ChowReciprocity s (embDivisor N) k' u' B') →
      ∃ m : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |chowSide (fun a => ‖σ a‖) s B v
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)|
            ≤ c * k := by sorry
