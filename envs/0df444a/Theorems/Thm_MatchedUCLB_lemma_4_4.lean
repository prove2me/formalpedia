-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_4_4
-- name    : MatchedUCLB.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:16.387198+00:00
-- url     : https://prove2.me/theorems/1dd936d1-06db-43c6-842a-7264b1a39a08
-- title:
--   Lemma 4.4 — the phase function $A_j$: convexity, smoothness, chain formulas on short prefixes, affine continuation
-- statement:
--   Let $q=p+\nu$ with $p\ge2$, $0<\nu\le1$. There is a constant $C_A>0$ depending only on $p,\nu$ such that the following holds. Let $m\ge1$, $\lambda,\tau>0$ and $G,s',t'\ge0$. Let $c\in\mathbb R^d$, let $v,u_1,\dots,u_m$ be orthonormal, and let either $v'=0$ and $s'=t'=0$ (the terminal phase), or $v'$ be a unit vector orthogonal to $E=\operatorname{span}\{v,u_1,\dots,u_m\}$. Let $h$, $R=\|h\|$, $\Gamma$, $s=\Gamma+Gt^\star/R$, $b=(G/R)h$, $g=sv-s'v'-b$, $\alpha$, $\delta=c_1\lambda m\tau^q$ and the functions $Q,P,I,O,A$ be those of (4.9)–(4.13), so that $A=M_\delta(I,O)$. Assume (4.14):
--
--   $$
--   G\le c_0\Gamma,\qquad \alpha^{-\frac1{q-1}}(s')^{\frac q{q-1}}\le c_0\lambda m\tau^q,\qquad s't'+\frac\alpha q(t')^q\le c_0\lambda m\tau^q .
--   $$
--
--   Then:
--
--   1. **(a)** $A$ is convex and $p$ times continuously differentiable with $\|\nabla^pA(x)-\nabla^pA(y)\|\le C_A\lambda\|x-y\|^\nu$;
--   2. **(b)** for $0\le b\le\lfloor m/4\rfloor$ and $w\in U_b=\operatorname{span}\{v,u_1,\dots,u_b\}$: $O(c+w)-I(c+w)\ge7\delta$; $A=O$ near $c+w$; $A(c+w)=Q(c+w)-\lambda(m+1)\tau^q/q-4\delta$; for $1\le k\le p$,
--   $$
--   \nabla^kA(c+w)[a_1,\dots,a_k]=\nabla^kQ(c+w)\bigl[P_{U_{b+1}}a_1,\dots,P_{U_{b+1}}a_k\bigr];
--   $$
--   and the value and these tensors at $c+w$ do not change when $u_{b+2},\dots,u_m$ and (when present) $v'$ are replaced by any other orthonormal completion;
--   3. **(c)** $A=I$ on a neighborhood of the segment $\{c+h+tv':0\le t\le t'\}$, where moreover $\nabla A=g$ and $\nabla^kA=0$ for $2\le k\le p$; $A(c+h)=0$ and $A(c+h+t'v')=-s't'$;
--   4. **(d)** $A(c)=-\lambda(m+1)\tau^q/q-4\delta$ and $\nabla^kA(c)=0$ for $1\le k\le p$.
--
--   For the terminal phase the segment reduces to the single point $c+h$. The lemma isolates the hardness of one phase: on short prefixes the phase function reveals at most one new chain direction per oracle call, and after the phase it is affine with a prescribed gradient.
--
--   **Formalization Note** All functions are the ambient ones of (4.13) and Definition E.8; the local points $(w,0)$ and $(h,t)$ become $c+w$ and $c+h+tv'$. Chain directions are indexed from $0$ in Lean, so "$u_{b+2},\dots,u_m$ vary" is "$u'_i=u_i$ for $0$-based $i\le b$". $P_{U_{b+1}}$ is the orthogonal projection `starProjection` onto $U_{b+1}$.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: local functions of (w, t_{j+1}) and statements at (w, 0), near (h_j, t_{j+1}) → ambient functions of (4.13) and statements at c + w and on a neighborhood (𝓝ˢ) of {c + h + t•vN : t ∈ [0, tN]}; reason: the ambient function depends on x only through the local coordinates (P_{E_j}(x − c_j), ⟨v_{j+1}, x − c_j⟩), so the two forms are equivalent
--   - encoding: terminal phase: t_L, v_L omitted, s_L = t⋆_L = 0, s_L v_L := 0 → vN = 0, sN = 0, tN = 0; reason: the page's own convention; the next coordinate and the α-term vanish identically
--   - reading: E_j with orthonormal basis v_j, u_{j,1..m} and next direction v_{j+1} (the setting of (4.9)–(4.13)) → hypotheses: {v} ∪ {u i} orthonormal; vN = 0 (terminal) or vN a unit vector orthogonal to v and every u i; reason: these are the standing assumptions under which (4.13) defines A_j on ℝ^d
--   - reading: unchanged by varying the remaining chain directions and, when present, v_{j+1} in an orthonormal completion → for every u' with {v} ∪ {u' i} orthonormal and u' i = u i for 0-based i ≤ b, and every vN' that is 0 exactly when vN is and otherwise a unit vector orthogonal to v and every u' i, the value and the tensors of order 1..p at c + w agree; reason: the remaining chain directions are those outside U_{j,b+1}
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.4, p.9, Eqs. (4.9)–(4.14)

import Mathlib
import Definitions.Def_MatchedUCLB_phaseA
import Definitions.Def_MatchedUCLB_chainPrefix
import Definitions.Def_MatchedUCLB_HolderBound
import Definitions.Def_MatchedUCLB_c0
import Definitions.Def_MatchedUCLB_Gam

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma 4.4 (the phase function).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.4, p.9: "There is a constant `C_A > 0`,
depending only on `p, ν`, with the following property. In Eqs. (4.9)–(4.12), take `m ≥ 1`,
`λ, τ_j > 0`, and `G_j, s_{j+1}, t⋆_{j+1} ≥ 0`. Define `b_j = (G_j/R_j)h_j` and the slope by Eq. (4.11),
using the scalar parameters above. Assume `G_j ≤ c_0Γ_j`, `α^{−1/(q−1)} s_{j+1}^{q/(q−1)} ≤ c_0λmτ_j^q`,
`s_{j+1}t⋆_{j+1} + (α/q)(t⋆_{j+1})^q ≤ c_0λmτ_j^q` (4.14). (a) `A_j` is convex and `C^{p,ν}`, with
`‖∇^pA_j(x) − ∇^pA_j(y)‖ ≤ C_Aλ‖x − y‖^ν` … (b) For every `w ∈ U_{j,b}` and `0 ≤ b ≤ ⌊m/4⌋`,
`O_j(w, 0) − I_j(w, 0) ≥ 7δ_j`, and … `A_j = O_j` near `c_j + w`. In particular,
`A_j(c_j + w) = Q_j(w) − λ(m+1)τ_j^q/q − 4δ_j`. For `1 ≤ k ≤ p` and all `a_1, …, a_k`,
`∇^kA_j(c_j + w)[a_1, …, a_k] = ∇^kQ_j(w)[P_{U_{j,b+1}}a_1, …, P_{U_{j,b+1}}a_k]`. The value and these
tensors are unchanged by varying the remaining chain directions and, when present, `v_{j+1}` in an
orthonormal completion. (c) `A_j = I_j` near `{(h_j, t_{j+1}) : 0 ≤ t_{j+1} ≤ t⋆_{j+1}}`. On a
neighborhood of `{c_j + h_j + tv_{j+1} : 0 ≤ t ≤ t⋆_{j+1}}` …, `∇A_j = g_j` and `∇^kA_j = 0` for
`2 ≤ k ≤ p`. Its values at the two endpoints are `0` and `−s_{j+1}t⋆_{j+1}`. (d) `A_j(0, 0) =
−λ(m+1)τ_j^q/q − 4δ_j` and `∇^kA_j(0, 0) = 0` for `1 ≤ k ≤ p`. The terminal phase satisfies the
same conclusions with the next coordinate omitted and the completed segment reduced to `{c_L}`."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. `A_j` is the ambient phase function `phaseA` of (4.13) / Definition
E.8 with `lam` = λ, `τ` = τ_j, `G` = G_j, `sN` = s_{j+1}, `tN` = t⋆_{j+1}, center `c` = c_j, starting
direction `v` = v_j, chain directions `u i` = u_{j,i+1} (0-based) and next direction `vN` = v_{j+1}.
The hypothesis on the directions is that `v_j, u_{j,1}, …, u_{j,m}` are orthonormal and that either
the phase is terminal (`vN = 0`, `s_{j+1} = t⋆_{j+1} = 0`) or `v_{j+1}` is a unit vector orthogonal
to `E_j`; this is the setting of (4.13). Local statements at `(w, 0)` and near `(h_j, t)` are stated at
the ambient points `c + w` and `c + h_j + t v_{j+1}` (the ambient function depends on `x` only through
the local coordinates, so the two forms are equivalent). `P_{U_{j,b+1}}` is the orthogonal projection
`starProjection` onto `chainPrefix v u (b + 1)` = `span{v_j, u_{j,1}, …, u_{j,b+1}}`, and `∇^kQ_j(w)`
is the derivative of the ambient chain `chainQ` at `c + w`. "Varying the remaining chain directions
and `v_{j+1}`" is any other orthonormal `(u', v_{j+1}')` with `u'_{j,i} = u_{j,i}` for `i ≤ b+1`
(0-based `i ≤ b`), terminal exactly when the original is. -/
theorem lemma_4_4 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∃ CA : ℝ, 0 < CA ∧
    ∀ (d m : ℕ) (lam τ G sN tN : ℝ) (c v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)),
      1 ≤ m → 0 < lam → 0 < τ → 0 ≤ G → 0 ≤ sN → 0 ≤ tN →
      Orthonormal ℝ (fun o : Option (Fin m) => Option.elim o v u) →
      ((vN = 0 ∧ sN = 0 ∧ tN = 0) ∨
        (‖vN‖ = 1 ∧ inner ℝ vN v = 0 ∧ ∀ i : Fin m, inner ℝ vN (u i) = 0)) →
      G ≤ c0 q * Gam q m lam τ →
      alphaC q m lam ^ (-1 / (q - 1)) * sN ^ (q / (q - 1)) ≤ c0 q * lam * m * τ ^ q →
      sN * tN + alphaC q m lam / q * tN ^ q ≤ c0 q * lam * m * τ ^ q →
      -- (a)
      (ConvexOn ℝ Set.univ (phaseA q lam τ G sN c v vN u) ∧ ContDiff ℝ p (phaseA q lam τ G sN c v vN u) ∧ HolderBound p ν (CA * lam) (phaseA q lam τ G sN c v vN u)) ∧
      -- (b)
      (∀ b : ℕ, b ≤ m / 4 → ∀ w ∈ chainPrefix v u b,
        7 * deltaC q m lam τ ≤ phaseO q lam τ c v vN u (c + w) - phaseI q lam τ G sN c v vN u (c + w) ∧
        (phaseA q lam τ G sN c v vN u) =ᶠ[𝓝 (c + w)] phaseO q lam τ c v vN u ∧
        phaseA q lam τ G sN c v vN u (c + w) = chainQ q lam c v u (c + w) - lam * (m + 1) * τ ^ q / q - 4 * deltaC q m lam τ ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ p → ∀ a : Fin k → EuclideanSpace ℝ (Fin d),
          iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) (c + w) a =
            iteratedFDeriv ℝ k (chainQ q lam c v u) (c + w)
              (fun i => (chainPrefix v u (b + 1)).starProjection (a i))) ∧
        (∀ (u' : Fin m → EuclideanSpace ℝ (Fin d)) (vN' : EuclideanSpace ℝ (Fin d)),
          Orthonormal ℝ (fun o : Option (Fin m) => Option.elim o v u') →
          ((vN = 0 ∧ vN' = 0) ∨
            (vN ≠ 0 ∧ ‖vN'‖ = 1 ∧ inner ℝ vN' v = 0 ∧ ∀ i : Fin m, inner ℝ vN' (u' i) = 0)) →
          (∀ i : Fin m, (i : ℕ) ≤ b → u' i = u i) →
          phaseA q lam τ G sN c v vN' u' (c + w) = phaseA q lam τ G sN c v vN u (c + w) ∧
          ∀ k : ℕ, 1 ≤ k → k ≤ p →
            iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN' u') (c + w) =
              iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) (c + w))) ∧
      -- (c)
      ((phaseA q lam τ G sN c v vN u) =ᶠ[𝓝ˢ ((fun t : ℝ => c + phaseH τ v u + t • vN) '' Set.Icc 0 tN)]
          phaseI q lam τ G sN c v vN u ∧
        (∀ᶠ x in 𝓝ˢ ((fun t : ℝ => c + phaseH τ v u + t • vN) '' Set.Icc 0 tN),
          gradient (phaseA q lam τ G sN c v vN u) x = gVec q lam τ G sN v vN u ∧
          ∀ k : ℕ, 2 ≤ k → k ≤ p → iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) x = 0) ∧
        phaseA q lam τ G sN c v vN u (c + phaseH τ v u) = 0 ∧
        phaseA q lam τ G sN c v vN u (c + phaseH τ v u + tN • vN) = -(sN * tN)) ∧
      -- (d)
      (phaseA q lam τ G sN c v vN u c = -(lam * (m + 1) * τ ^ q / q) - 4 * deltaC q m lam τ ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ p → iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) c = 0) := by sorry

end MatchedUCLB
