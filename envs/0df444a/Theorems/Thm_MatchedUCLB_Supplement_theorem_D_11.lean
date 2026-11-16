-- Prove2me | Theorems.Thm_MatchedUCLB_Supplement_theorem_D_11
-- name    : MatchedUCLB.Supplement.theorem_D_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:59:35.68079+00:00
-- url     : https://prove2.me/theorems/e77184fb-309b-48fa-add9-21c9bb36ba60
-- title:
--   Theorem D.11 — the phase function $A_j=M_{\delta_j}(I_j,O_j)$: $A_j\ge\max\{I_j,O_j\}$, excess $7\delta_j$ on short chain prefixes, endpoint data (D.31)–(D.35), $C_A\lambda$-Hölder $p$th derivative
-- statement:
--   This is the appendix form of the phase-function lemma of the construction (Theorem D.11 of the paper; its main-text restatement is Lemma 4.4).
--
--   Let $p\ge2$ be an integer, $0<\nu\le1$ and $q=p+\nu$, $q^*=q/(q-1)$. There is a constant $C_A>0$, depending only on $p$ and $\nu$, such that the following holds. Let $m\ge1$, $\lambda,\tau>0$ and $G,s',t'\ge0$. Let $c\in\mathbb R^d$, let $v,u_1,\dots,u_m$ be orthonormal and $E=\operatorname{span}\{v,u_1,\dots,u_m\}$, and let either $v'=0$ and $s'=t'=0$ (the terminal phase), or $v'$ be a unit vector orthogonal to $E$. Put
--
--   $$
--   \Gamma=\frac{\lambda\tau^{q-1}}{\sqrt m},\quad t^\star=\sqrt m\,(m+1)\tau,\quad h=t^\star v+\sum_{i=1}^m(m-i+1)\tau u_i,\quad R=\|h\|,
--   $$
--
--   $$
--   b=\frac GR h,\quad s=\Gamma+\frac{Gt^\star}{R},\quad \alpha=\lambda m^{1-\frac{3q}2},\quad \mathcal E=\lambda m\tau^q,\quad \delta=c_1\mathcal E,\quad g=sv-s'v'-b,
--   $$
--
--   with $c_0=c_1=2^{-q-3}/q$, and let $Q,P,I,O,A=M_\delta(I,O)$ be the chain, regularized chain, affine continuation, shifted chain and phase function of (D.13)–(D.17), extended to $\mathbb R^d$ by (4.13). Assume
--
--   $$
--   G\le c_0\Gamma,\qquad s't'+\frac{\alpha(t')^q}{q}\le c_0\mathcal E,\qquad \alpha^{-\frac1{q-1}}(s')^{q^*}\le c_0\mathcal E .
--   $$
--
--   Write $U_b=\operatorname{span}\{v,u_1,\dots,u_b\}$. Then:
--
--   1. **(a) Convexity.** $A$ is convex and $A\ge\max\{I,O\}$ on $\mathbb R^d$.
--   2. **(b) Chain-prefix excess and oracle output.** For every integer $0\le b\le\lfloor m/4\rfloor$ and every $w\in U_b$ (no bound on $\|w\|$): $O(c+w)-I(c+w)\ge7\delta$ and $A=O$ near $c+w$; $A(c+w)=Q(c+w)-\frac\lambda q(m+1)\tau^q-4\delta$; for $1\le k\le p$,
--   $$
--   \nabla^kA(c+w)[a_1,\dots,a_k]=\nabla^kQ(c+w)\bigl[P_{U_{b+1}}a_1,\dots,P_{U_{b+1}}a_k\bigr];
--   $$
--   and this value and these derivatives depend only on $v,u_1,\dots,u_{b+1}$: they are unchanged when $u_{b+2},\dots,u_m$ and (when present) $v'$ are replaced by any other orthonormal completion.
--   3. **(c) Affine region.** $A=I$ on a neighborhood of the segment $\{c+h+tv':0\le t\le t'\}$, and
--   $$
--   A(c+h)=0,\quad A(c+h+t'v')=-s't',\quad \nabla A(c+h)=\nabla A(c+h+t'v')=g,\quad \nabla^kA(c+h)=\nabla^kA(c+h+t'v')=0\ (2\le k\le p).
--   $$
--   4. **(d) Starting derivatives and gradient change.** $A(c)=-\frac\lambda q(m+1)\tau^q-4\delta$ and $\nabla^kA(c)=0$ for $1\le k\le p$; consequently
--   $$
--   b+\bigl(\nabla A(c+h)-\nabla A(c)\bigr)=b+g=sv-s'v'.
--   $$
--   5. **(e) Smoothness.** $A$ is $p$ times continuously differentiable and $\|\nabla^pA(x)-\nabla^pA(y)\|\le C_A\lambda\|x-y\|^\nu$ for all $x,y$.
--   6. **(f) Terminal phase.** All of (a)–(e) hold in the terminal case $v'=0$, $s'=t'=0$, where the segment of (c) is the single point $c+h$.
--
--   One phase of the hard instance hides its chain: on short prefixes the oracle output comes from the shifted chain and reveals at most one new direction per call, and after the phase the function is affine with the prescribed gradient $g$, so the phases can be glued. Compared with Lemma 4.4, the theorem adds $A\ge\max\{I,O\}$ and states the endpoint gradients and the identity (D.35) as point values.
--
--   **Formalization Note** All functions are the published ambient ones (`phaseA`, `phaseI`, `phaseO`, `chainQ`) of (4.13) and Definition E.8; the local points $(w,0)$, $(h,t)$ and $(0,0)$ become $c+w$, $c+h+tv'$ and $c$. Chain directions are indexed from $0$ in Lean, so "$u_{b+2},\dots,u_m$ vary" is "$u'_i=u_i$ for $0$-based $i\le b$". $P_{U_{b+1}}$ is the orthogonal projection `starProjection` onto $U_{b+1}$. $C_A$ is chosen after $p,\nu,q$ and before all phase data.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇F, ∇^kF → EuclideanSpace ℝ (Fin d), gradient, iteratedFDeriv ℝ k; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: local functions of (w, t_{j+1}) and statements at (w, 0), near (h_j, t_{j+1}), at (h_j, 0), (h_j, t⋆_{j+1}), (0, 0) → ambient functions of (4.13) and statements at c + w, on a neighborhood (𝓝ˢ) of {c + h + t•vN : t ∈ [0, tN]}, at c + h, c + h + tN•vN, c; reason: the ambient function depends on x only through the local coordinates (P_{E_j}(x − c_j), ⟨v_{j+1}, x − c_j⟩), so the two forms are equivalent
--   - encoding: (f) terminal phase with s_L = t⋆_L = 0, v_L omitted, functions restricted to t_{j+1} = 0 → the disjunct vN = 0, sN = 0, tN = 0 of the direction hypothesis, under which all of (a)–(e) are asserted; reason: with vN = 0 the next coordinate ⟨vN, x − c⟩ and the α-term vanish identically, which is the restriction to t_{j+1} = 0
--   - reading: an orthonormal block as in (D.7)–(D.8), and for j < L−1 a unit v_{j+1} ⊥ E_j → hypotheses: {v} ∪ {u i} orthonormal; vN = 0 (terminal) or vN a unit vector orthogonal to v and every u i; reason: these are the standing assumptions under which (D.15)–(D.17) and (4.13) define A_j on ℝ^d; the phase index j and L only select terminal or not
--   - reading: the value and full ambient derivatives through order p, given by (D.36)–(D.37), depend only on v_j, u_{j,1}, …, u_{j,b+1} and fixed scalars → the explicit value A(c+w) = Q(c+w) − λ(m+1)τ^q/q − 4δ, the derivative formula ∇^kA(c+w)[a] = ∇^kQ(c+w)[P_{U_{b+1}}a] for 1 ≤ k ≤ p (the page's own rewriting of (D.36), p.70), and invariance of the value and the derivatives of orders 1..p at c + w under every other orthonormal completion u' with u' i = u i for 0-based i ≤ b and every vN' that is 0 exactly when vN is and otherwise a unit vector orthogonal to v and every u' i; reason: (D.37) equals Q_j(w) − λ(m+1)τ^q/q − 4δ_j because the residuals of w ∈ U_{j,b} beyond row b vanish, and the completions are what "depend only on" ranges over
--   - encoding: A_j ∈ C^{p,ν} → ContDiff ℝ p and HolderBound p ν (CA * lam); reason: C^{p,ν} is p-fold continuous differentiability with a ν-Hölder pth derivative, whose constant is the one stated in (e)
--   - encoding: C_A in (D.47) depending only on p, ν and the fixed smoothing function → ∃ CA > 0 quantified after p, ν, q and before every phase parameter; reason: the smoothing function φ of the published smoothMax is fixed, so dependence on it is no dependence on the phase
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Theorem D.11, pp.68–69 (PDF pp.69–70), with Eqs. (D.7)–(D.8), (D.13)–(D.17), (D.24), (D.26), (D.29)–(D.37)

import Mathlib
import Definitions.Def_MatchedUCLB_phaseA
import Definitions.Def_MatchedUCLB_phaseI
import Definitions.Def_MatchedUCLB_phaseO
import Definitions.Def_MatchedUCLB_phaseH
import Definitions.Def_MatchedUCLB_gVec
import Definitions.Def_MatchedUCLB_slope
import Definitions.Def_MatchedUCLB_Gam
import Definitions.Def_MatchedUCLB_alphaC
import Definitions.Def_MatchedUCLB_deltaC
import Definitions.Def_MatchedUCLB_c0
import Definitions.Def_MatchedUCLB_chainQ
import Definitions.Def_MatchedUCLB_chainPrefix
import Definitions.Def_MatchedUCLB_HolderBound

open scoped ContDiff Topology

namespace MatchedUCLB.Supplement

/-- **Theorem D.11 (Phase function with `A_j − I_j ≥ 7δ_j` on short chain prefixes).** Bai,
*Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*,
arXiv:2611.05527, Theorem D.11, pp.68–69 (PDF pp.69–70), Appx. D.1.5, with Eqs. (D.7)–(D.8),
(D.13)–(D.17), (D.24), (D.26), (D.29)–(D.37).

"Fix a phase `0 ≤ j < L`, `p ≥ 2`, `0 < ν ≤ 1`, `q = p + ν`, and an orthonormal block as in
Eq. (D.7)–(D.8). Take `m ≥ 1`, `λ, τ_j > 0`, `G_j, s_{j+1}, t⋆_{j+1} ≥ 0` … Assume `G_j ≤ c_0Γ_j`,
`s_{j+1}t⋆_{j+1} + α(t⋆_{j+1})^q/q ≤ c_0E_j` (D.26), `α^{−1/(q−1)} s_{j+1}^{q*} ≤ c_0E_j` (D.29).
(a) `A_j` is convex and `A_j ≥ max{I_j, O_j}`. (b) For every integer `0 ≤ b ≤ ⌊m/4⌋` and every
`w ∈ U_{j,b}`, `O_j(w,0) − I_j(w,0) ≥ 7δ_j`, `A_j = O_j` near `(w,0)`; the value and full ambient
derivatives through order `p`, given by (D.36)–(D.37), depend only on `v_j, u_{j,1}, …, u_{j,b+1}`
and fixed scalars. (c) `A_j = I_j` near `{(h_j, t_{j+1}) : 0 ≤ t_{j+1} ≤ t⋆_{j+1}}`, and (D.31)–(D.33).
(d) (D.34) and, consequently, (D.35). (e) `A_j ∈ C^{p,ν}` and
`‖∇^pA_j(x) − ∇^pA_j(y)‖ ≤ C_Aλ‖x − y‖^ν`, where `C_A` depends only on `p, ν` and the fixed smoothing
function. (f) For `j = L − 1`, parts (a)–(e) hold with `s_L = t⋆_L = 0`, `v_L` omitted, and the
functions restricted to `t_{j+1} = 0`."

**Formalization Note.**
* `q` is a real binder with the hypothesis `q = p + ν`; powers with real exponents are `Real.rpow`;
  `q* = q/(q − 1)`, `E_j = λmτ_j^q`.
* `A_j, I_j, O_j` are the published ambient functions `phaseA`, `phaseI`, `phaseO` (Eq. (4.13),
  Definition E.8) with `lam` = λ, `τ` = τ_j, `G` = G_j, `sN` = s_{j+1}, `tN` = t⋆_{j+1}, center
  `c` = c_j, `v` = v_j, chain directions `u i` = u_{j,i+1} (0-based) and `vN` = v_{j+1}. The local
  points `(w, 0)` and `(h_j, t)` are the ambient points `c + w` and `c + h_j + t • vN`; `(0,0)` is `c`.
* The orthonormal block is the hypothesis that `v, u 0, …, u (m−1)` are orthonormal. The phase is
  either terminal (`vN = 0`, `sN = tN = 0`: part (f), the next coordinate is identically `0`) or
  `vN` is a unit vector orthogonal to `E_j`.
* `b_j = (G_j/R_j) h_j` with `R_j = ‖h_j‖`; `g_j` is `gVec`, `s_j` is `slope`, `δ_j` is `deltaC`.
* (b): "the value and derivatives given by (D.36)–(D.37)" are stated as
  `A_j(c+w) = Q_j(w) − λ(m+1)τ_j^q/q − 4δ_j` and
  `∇^kA_j(c+w)[a] = ∇^kQ_j(w)[P_{U_{j,b+1}}a_1, …, P_{U_{j,b+1}}a_k]` (the page's own rewriting of
  (D.36), p.70), with `P` the orthogonal projection `starProjection` onto `chainPrefix v u (b+1)`.
  "Depend only on `v_j, u_{j,1..b+1}`" is: for every other orthonormal completion `u'` agreeing with
  `u` at 0-based indices `≤ b`, and every `vN'` that is `0` exactly when `vN` is and otherwise a unit
  vector orthogonal to `v` and all `u' i`, the value and the derivatives of orders `1..p` at `c + w`
  are unchanged.
* (e): `C^{p,ν}` is `ContDiff ℝ p` together with the published `HolderBound p ν (C_A λ)`. `C_A` is
  chosen after `p, ν, q` and before every phase parameter. -/
theorem theorem_D_11 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∃ CA : ℝ, 0 < CA ∧
    ∀ (d m : ℕ) (lam τ G sN tN : ℝ) (c v vN : EuclideanSpace ℝ (Fin d))
      (u : Fin m → EuclideanSpace ℝ (Fin d)),
      1 ≤ m → 0 < lam → 0 < τ → 0 ≤ G → 0 ≤ sN → 0 ≤ tN →
      Orthonormal ℝ (fun o : Option (Fin m) => Option.elim o v u) →
      ((vN = 0 ∧ sN = 0 ∧ tN = 0) ∨
        (‖vN‖ = 1 ∧ inner ℝ vN v = 0 ∧ ∀ i : Fin m, inner ℝ vN (u i) = 0)) →
      G ≤ c0 q * Gam q m lam τ →
      sN * tN + alphaC q m lam * tN ^ q / q ≤ c0 q * (lam * m * τ ^ q) →
      alphaC q m lam ^ (-1 / (q - 1)) * sN ^ (q / (q - 1)) ≤ c0 q * (lam * m * τ ^ q) →
      -- (a) Convexity
      (ConvexOn ℝ Set.univ (phaseA q lam τ G sN c v vN u) ∧
        ∀ x : EuclideanSpace ℝ (Fin d),
          max (phaseI q lam τ G sN c v vN u x) (phaseO q lam τ c v vN u x) ≤
            phaseA q lam τ G sN c v vN u x) ∧
      -- (b) Chain-prefix excess and oracle output
      (∀ b : ℕ, b ≤ m / 4 → ∀ w ∈ chainPrefix v u b,
        7 * deltaC q m lam τ ≤
            phaseO q lam τ c v vN u (c + w) - phaseI q lam τ G sN c v vN u (c + w) ∧
        (phaseA q lam τ G sN c v vN u) =ᶠ[𝓝 (c + w)] phaseO q lam τ c v vN u ∧
        phaseA q lam τ G sN c v vN u (c + w) =
            chainQ q lam c v u (c + w) - lam / q * (m + 1) * τ ^ q - 4 * deltaC q m lam τ ∧
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
      -- (c) Affine region, (D.31)–(D.33)
      ((phaseA q lam τ G sN c v vN u)
          =ᶠ[𝓝ˢ ((fun t : ℝ => c + phaseH τ v u + t • vN) '' Set.Icc 0 tN)]
          phaseI q lam τ G sN c v vN u ∧
        phaseA q lam τ G sN c v vN u (c + phaseH τ v u) = 0 ∧
        phaseA q lam τ G sN c v vN u (c + phaseH τ v u + tN • vN) = -(sN * tN) ∧
        gradient (phaseA q lam τ G sN c v vN u) (c + phaseH τ v u) = gVec q lam τ G sN v vN u ∧
        gradient (phaseA q lam τ G sN c v vN u) (c + phaseH τ v u + tN • vN) =
          gVec q lam τ G sN v vN u ∧
        (∀ k : ℕ, 2 ≤ k → k ≤ p →
          iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) (c + phaseH τ v u) = 0 ∧
          iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) (c + phaseH τ v u + tN • vN) = 0)) ∧
      -- (d) Starting derivatives (D.34) and gradient change (D.35)
      (phaseA q lam τ G sN c v vN u c = -(lam / q * (m + 1) * τ ^ q) - 4 * deltaC q m lam τ ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ p → iteratedFDeriv ℝ k (phaseA q lam τ G sN c v vN u) c = 0) ∧
        (G / ‖phaseH τ v u‖) • phaseH τ v u +
            (gradient (phaseA q lam τ G sN c v vN u) (c + phaseH τ v u) -
              gradient (phaseA q lam τ G sN c v vN u) c) =
          (G / ‖phaseH τ v u‖) • phaseH τ v u + gVec q lam τ G sN v vN u ∧
        (G / ‖phaseH τ v u‖) • phaseH τ v u + gVec q lam τ G sN v vN u =
          slope q lam τ G v u • v - sN • vN) ∧
      -- (e) Smoothness
      (ContDiff ℝ p (phaseA q lam τ G sN c v vN u) ∧
        HolderBound p ν (CA * lam) (phaseA q lam τ G sN c v vN u)) := by sorry

end MatchedUCLB.Supplement
