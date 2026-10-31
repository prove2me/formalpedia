-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_4
-- name    : HuberSNSDP.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:19.18877+00:00
-- url     : https://prove2.me/theorems/d909e0cf-cf1c-4ab6-a819-16fd76842eeb
-- title:
--   Lemma 4 (corrected: leading $P$, coupled sign, restricted Moreover clause) — structure of $\partial_B\Phi(0,W)$ and $\partial\Phi(0,W)$
-- statement:
--   Let $W\in\mathbb S^n$ have the spectral decomposition $W=P\,\mathrm{diag}(d)P^T$, with index sets $\alpha,\beta,\gamma$ of positive, zero and negative $d_i$, and write $\tilde H=P^THP$ and $p_i$ for the $i$-th column of $P$. For $V_{|\beta|}:\mathbb R\times\mathbb S^{|\beta|}\to\mathbb S^{|\beta|}$ and $v\in\mathbb R$ let
--   $$\mathfrak B(V_{|\beta|},v)(\tau,H)=P\begin{pmatrix}\tilde H_{\alpha\alpha}&\tilde H_{\alpha\beta}&[\Omega_0(d)]_{\alpha\gamma}\circ\tilde H_{\alpha\gamma}\\ \tilde H_{\alpha\beta}^T&V_{|\beta|}(\tau,\tilde H_{\beta\beta})&0\\ \tilde H_{\alpha\gamma}^T\circ[\Omega_0(d)]_{\alpha\gamma}^T&0&0\end{pmatrix}P^T+\frac{v\tau}{2}\sum_{i\in\alpha}p_ip_i^T .$$
--   Call $(V_{|\beta|},v)$ a **coupled pair** if $V_{|\beta|}\in\partial_B\Phi_{|\beta|}(0,0)$, $v\in\{-1,1\}$ and $vV_{|\beta|}(1,0)\succeq0$. Then:
--
--   1. $V\in\partial_B\Phi(0,W)$ if and only if $V=\mathfrak B(V_{|\beta|},v)$ for some coupled pair;
--   2. $V\in\partial\Phi(0,W)$ if and only if $V=\mathfrak B(V_{|\beta|},v)$ for some $(V_{|\beta|},v)$ in the convex hull of the coupled pairs;
--   3. the maps $Y\mapsto V_{|\beta|}(0,Y)$ with $V_{|\beta|}\in\partial_B\Phi_{|\beta|}(0,0)$ are exactly the maps $Y\mapsto U[\Omega_{|\beta|}\circ(U^TYU)]U^T$ with $U\in\mathbb R^{|\beta|\times|\beta|}$ orthogonal and
--   $$\Omega_{|\beta|}\in\Big\{\lim_{k\to\infty}\Omega(\epsilon^k,z^k):(\epsilon^k,z^k)\to(0,0),\ \epsilon^k\neq0,\ z^k_1\ge\dots\ge z^k_{|\beta|}\Big\}.$$
--
--   This describes the generalized Jacobians of $\Phi$ at $\epsilon=0$; it is the main tool in the proofs of (17), Lemma 5, Lemma 9 and Proposition 2.
--
--   **Formalization Note** $\Phi_{|\beta|}$ is the same Huber smoothing on $\mathbb S^{|\beta|}$; generalized Jacobians are those of $\Phi$ as a map on $\mathbb R\times\mathbb S^n$.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - correction: $V(\tau,H)=\begin{pmatrix}\cdots\end{pmatrix}P^T+\frac{v\tau}{2}\sum_{i\in\alpha}p_ip_i^T$ (no leading $P$) → $P\begin{pmatrix}\cdots\end{pmatrix}P^T+\frac{v\tau}{2}\sum_{i\in\alpha}p_ip_i^T$; reason: typographical: the printed right side is not symmetric in general; (16) on p.10, Lemma 1 on p.6 and Appendix I (p.43) all carry the leading $P$
--   - correction: $V\in\partial_B\Phi(0,W)$ iff $V=\mathfrak B(V_{|\beta|},v)$ with $V_{|\beta|}\in\partial_B\Phi_{|\beta|}(0,0)$ and $v\in\{-1,1\}$ chosen independently → the pair must also satisfy $vV_{|\beta|}(1,0)\succeq0$; reason: counterexample to the printed "if": $n=2$, $W=\mathrm{diag}(1,0)$, $P=I$, $V_{|\beta|}(\tau,y)=y-\tau/2$ (the limit of $\nabla h$ along $(1/k,2/k)$, so in $\partial_B\Phi_1(0,0)$), $v=+1$ gives $V(1,0)=\mathrm{diag}(1/2,-1/2)$; but every element of $\partial_B\Phi(0,W)$ has $\tau$-part $\mathrm{diag}(-s/2,c)$ with $s=\pm1$ and $sc\le0$, whose convex hull misses $\mathrm{diag}(1/2,-1/2)$; the sign of $v$ and of the $\tau$-part of $V_{|\beta|}$ are both $-\mathrm{sign}(\epsilon^k)$ along the defining sequence, and with the coupling both directions hold
--   - correction: $V\in\partial\Phi(0,W)$ iff $V=\mathfrak B(V_{|\beta|},v)$ with $V_{|\beta|}\in\partial\Phi_{|\beta|}(0,0)$ and $v\in[-1,1]$ chosen independently → $(V_{|\beta|},v)$ ranges over the convex hull of the coupled pairs; reason: the same counterexample lies in the printed Clarke set but not in $\partial\Phi(0,W)$; $\partial\Phi=\mathrm{conv}\,\partial_B\Phi$ and $\mathfrak B$ is affine in the pair, so the corrected B-part gives exactly this set
--   - correction: "Moreover, $V_{|\beta|}\in\partial_B\Phi_{|\beta|}(0,0)$ iff there exist $U$ orthogonal and $\Omega_{|\beta|}$ in the limit set with $V_{|\beta|}(0,Y)=U[\Omega_{|\beta|}\circ(U^TYU)]U^T$" → equality of the two sets of restrictions $Y\mapsto V_{|\beta|}(0,Y)$; reason: the right side constrains only $V_{|\beta|}(0,\cdot)$; counterexample: $|\beta|=1$, $V_{|\beta|}(\tau,y)=y$, $U=1$, $\Omega_{|\beta|}=1$ (the limit of $\Omega$ along $z^k=\epsilon^k=1/k$), yet $h'_2\to1$ forces $h'_1\to\mp1/2$, so no element of $\partial_B\Phi_1(0,0)$ has $\tau$-part $0$ and $h'_2$-part $1$
--   - encoding: the block matrix of Lemma 4 and $\Phi_{|\beta|}$ → the published `blockForm21 d H̃ (V_{|β|}(τ, H̃_ββ))` and `PhiPair` on `SymMat (betaIdx d)`; $V$ and $V_{|\beta|}$ are continuous linear maps on the pair spaces; reason: entry-by-entry the same matrix and the same map; elements of generalized Jacobians are linear maps
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 4, p.11 (proof: Appendix C)

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 4, p.11 (Liang, Sun & Toh, arXiv:2303.05825v4), corrected.

Let `W ∈ Sⁿ` have the spectral decomposition (7), `W = P diag(d) Pᵀ`, `α, β, γ` the index sets of
positive, zero and negative `dᵢ`, `H̃ = PᵀHP`, and `𝔅(V_{|β|}, v)(τ, H)` the matrix
`P [ H̃_αα, H̃_αβ, [Ω₀(d)]_αγ ∘ H̃_αγ ; H̃_αβᵀ, V_{|β|}(τ, H̃_ββ), 0 ; H̃_αγᵀ ∘ [Ω₀(d)]_αγᵀ, 0, 0 ] Pᵀ
+ (vτ/2) ∑_{i∈α} pᵢpᵢᵀ` (`lemma4Block`). Call `(V_{|β|}, v)` a coupled pair if
`V_{|β|} ∈ ∂_BΦ_{|β|}(0, 0)`, `v ∈ {−1, 1}` and `v V_{|β|}(1, 0) ⪰ 0` (`coupledPairs`). Then:
1. `V ∈ ∂_BΦ(0, W)` iff `V = 𝔅(V_{|β|}, v)` for some coupled pair;
2. `V ∈ ∂Φ(0, W)` iff `V = 𝔅(V_{|β|}, v)` for some `(V_{|β|}, v)` in the convex hull of the coupled
   pairs;
3. the restrictions `Y ↦ V_{|β|}(0, Y)` of the elements `V_{|β|} ∈ ∂_BΦ_{|β|}(0, 0)` are exactly the
   maps `Y ↦ U[Ω_{|β|} ∘ (UᵀYU)]Uᵀ` with `U ∈ ℝ^{|β|×|β|}` orthogonal and `Ω_{|β|}` in the limit set
   `{lim Ω(εᵏ, zᵏ) : (εᵏ, zᵏ) → (0, 0), εᵏ ≠ 0, z₁ᵏ ≥ ⋯ ≥ z_{|β|}ᵏ}` (`OmegaLimSet`).

**Formalization Note.** The printed lemma omits the leading `P` (restored as in (16)), lets
`V_{|β|}` and `v` vary independently (false in the "if" direction: see the mission notes), and
states the "Moreover" clause for `V_{|β|}` itself although its right side determines only
`V_{|β|}(0, ·)`; these are the three corrections. `Φ_{|β|}` is `PhiPair` on `SymMat β`. -/
theorem lemma_4 {n : ℕ} (W : SymMat (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hW : IsSpectralDecomp W P d) :
    (∀ V : RS (Fin n) →L[ℝ] SymMat (Fin n),
      V ∈ bJac (PhiPair (ι := Fin n)) (rsPt 0 W) ↔
        ∃ q ∈ coupledPairs d, ∀ x : RS (Fin n), (V x).toMat = lemma4Block P d q.1 q.2 x) ∧
    (∀ V : RS (Fin n) →L[ℝ] SymMat (Fin n),
      V ∈ clarkeJac (PhiPair (ι := Fin n)) (rsPt 0 W) ↔
        ∃ q ∈ convexHull ℝ (coupledPairs d),
          ∀ x : RS (Fin n), (V x).toMat = lemma4Block P d q.1 q.2 x) ∧
    {g : SymMat (betaIdx d) → SymMat (betaIdx d) |
        ∃ Vb ∈ bJac (PhiPair (ι := betaIdx d)) (rsPt 0 0), g = fun Y => Vb (rsPt 0 Y)} =
      {g | ∃ U ∈ Matrix.orthogonalGroup (betaIdx d) ℝ, ∃ Ω ∈ OmegaLimSet d,
        g = fun Y => SymMat.ofMat
          (U * Matrix.hadamard Ω (U.transpose * Y.toMat * U) * U.transpose)} := by sorry

end HuberSNSDP
