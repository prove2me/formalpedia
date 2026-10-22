-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_theorem_12
-- name    : LieTwoAlg.Equiv.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:45.240347+00:00
-- url     : https://prove2.me/theorems/7de493a6-0744-4ec9-bdf3-a1bd6d979b96
-- title:
--   Theorem 12, pp. 14–15 (2-cell part) — linear natural transformations correspond to chain homotopies
-- statement:
--   Let $V$ and $W$ be 2-vector spaces over a field $k$ and let $F,G\colon V\to W$ be linear functors. A **linear natural transformation** $\theta\colon F\Rightarrow G$ is a linear map $\theta\colon V_0\to W_1$ with $s(\theta_x)=F_0(x)$, $t(\theta_x)=G_0(x)$ and $F_1(f)\,\theta_{t(f)}=\theta_{s(f)}\,G_1(f)$ for every morphism $f$ of $V$ (composition written diagrammatically). Write $S(V)$ for the 2-term chain complex $\ker s\xrightarrow{\;t\;}V_0$ and $S(F)$ for the chain map $(F_0,F_1|_{\ker s})$. A **chain homotopy** $\tau\colon S(F)\Rightarrow S(G)$ is a linear map $\tau\colon V_0\to\ker s_W$ with
--
--   $$
--   t(\tau(x))=G_0(x)-F_0(x),\qquad \tau(t(h))=G_1(h)-F_1(h)\quad (h\in\ker s_V).
--   $$
--
--   Then taking arrow parts, $\theta\mapsto\big(x\mapsto\vec\theta_x=\theta_x-i(s(\theta_x))\big)$, is a bijection from linear natural transformations $F\Rightarrow G$ onto chain homotopies $S(F)\Rightarrow S(G)$.
--
--   This is the 2-morphism part of the 2-equivalence $\mathbf{2Vect}\simeq\mathbf{2Term}$ of Theorem 12, and it is what the proof of Theorem 36 uses to see that the comparison $F_2$ of a Lie 2-algebra homomorphism is a natural transformation.
--
--   **Formalization Note** Only the 2-cell correspondence of Theorem 12 is stated. The 1-cell part is Proposition 8 (a separate item); the 2-functoriality of $S,T$ and the 2-naturality of the comparison isomorphisms are not stated. The inverse bijection is the paper's $T(\tau)(x)=(\varphi_0(x),\tau(x))$, i.e. $\tau\mapsto i\circ F_0+\tau$.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 14–15, Theorem 12 and its proof, 2-cell part

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Theorem 12, pp. 14–15, 2-cell part: for linear functors `F G : V → W`, taking arrow parts
`θ ↦ (x ↦ θ⃗ₓ)` is a bijection from linear natural transformations `F ⇒ G` onto chain
homotopies `S(F) ⇒ S(G)`. -/
theorem theorem_12 {k : Type u} [Field k] {V W : TwoVect k} (F G : LinFunctor V W)
    (hF : IsLinFunctor F) (hG : IsLinFunctor G) :
    ∃ e : {θ : V.V0 →ₗ[k] W.V1 // IsLinNat F G θ} ≃
        {τ : V.V0 →ₗ[k] LinearMap.ker W.s //
          IsChainHtpy (toTwoTermMap F) (toTwoTermMap G) τ},
      ∀ (θ : {θ : V.V0 →ₗ[k] W.V1 // IsLinNat F G θ}) (x : V.V0),
        ((e θ).1 x : W.V1) = W.arrow (θ.1 x) := by sorry

end LieTwoAlg.Equiv
