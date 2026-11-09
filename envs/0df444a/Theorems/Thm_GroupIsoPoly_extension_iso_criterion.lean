-- Prove2me | Theorems.Thm_GroupIsoPoly_extension_iso_criterion
-- name    : GroupIsoPoly.extension_iso_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:53.758382+00:00
-- url     : https://prove2.me/theorems/ef351eb0-d1c8-462f-abef-599d13def952
-- title:
--   §9.2.2 — the extension-isomorphism criterion (9.5)–(9.6) ([GQ17, Lemma 2.3])
-- statement:
--   Let $p$ be a prime, $A=\mathbb F_p^a$, $Q$ a finite group, $\theta_G,\theta_H$ two linear actions of $Q$ on $A$ and $f_G,f_H$ normalised 2-cocycles for them, defining extension groups $E_G=E(\theta_G,f_G)$ and $E_H=E(\theta_H,f_H)$ on $A\times Q$ with $(u,q)(v,r)=(u+\theta(q)v+f(q,r),qr)$ as in (9.4). Let $\alpha\in\mathrm{GL}(A)$ and $\beta\in\mathrm{Aut}(Q)$.
--   1. For every $b:Q\to A$, the map $F(u,q)=(\alpha u+b(q),\beta q)$ is a group isomorphism $E_G\to E_H$ if and only if for all $q,r\in Q$
--   $$
--   \alpha\,\theta_G(q)=\theta_H(\beta q)\,\alpha, \tag{9.5}
--   $$
--   $$
--   b(q)+\theta_H(\beta q)\,b(r)-b(qr)=\alpha f_G(q,r)-f_H(\beta q,\beta r). \tag{9.6}
--   $$
--   2. If $(\alpha,\beta)$ is compatible, i.e. satisfies (9.5), then the induced map $(T_{\alpha,\beta}f)(q_1,\dots,q_j)=\alpha f(\beta^{-1}q_1,\dots,\beta^{-1}q_j)$ commutes with the differentials: $T_{\alpha,\beta}\circ d_{\theta_G}=d_{\theta_H}\circ T_{\alpha,\beta}$ in every degree.
--   3. If $(\alpha,\beta)$ is compatible, then (9.6) has a solution $b$ if and only if $[T_{\alpha,\beta}f_G]=[f_H]$ in $H^2(Q,A)$ for the action $\theta_H$, i.e. $T_{\alpha,\beta}f_G-f_H=d_{\theta_H}c$ for some 1-cochain $c$.
--
--   This is how the algorithm reduces isomorphism of extensions to matching actions (Theorem 9.3) and then matching cohomology classes (Theorem 9.4), and how it lifts the matched data back to isomorphisms by solving the linear system (9.6).
--
--   **Formalization Note** "Isomorphism" is a multiplicative bijection whose underlying map is $F$. Cochains are arbitrary maps $Q^j\to A$ with Mathlib's inhomogeneous differential.
--
--   Differences from the source:
--
--   - encoding: A ≅ F_p^a with characteristic kernels and quotients identified → A = `Fin a → ZMod p`, θ as a `Representation`, the two extensions on A × Q with the same Q and A; reason: the paper's own identification ("After identifying characteristic kernels with A and quotients with Q")
--   - encoding: b ∈ C¹(Q, A) (normalised cochains) → b : Q → A arbitrary; cochains of every degree arbitrary maps Q^j → A; reason: (9.6) at q = r = 1 forces b(1) = 0, and the normalised subcomplex computes the same cohomology (p.95)
--   - encoding: [T_{α,β} f_G] = [f_H] → T_{α,β} f_G − f_H = d_{θ_H} c for a 1-cochain c; reason: equality of classes in H² is equality modulo coboundaries
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, (9.4)–(9.6), p.95 (PDF p.99)

import Mathlib
import Definitions.Def_GroupIsoPoly_Ext
import Definitions.Def_GroupIsoPoly_coboundary

set_option autoImplicit false

namespace GroupIsoPoly

/-- **§9.2.2 — the extension-isomorphism criterion** ([GQ17, Lemma 2.3]).

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, p.95 (PDF p.99): "In the coordinates above,
F(u, q) = (αu + b(q), βq) is an isomorphism precisely when αθG(q) = θH(βq)α, (9.5)
b(q) + θH(βq)b(r) − b(qr) = αfG(q, r) − fH(βq, βr). (9.6) Here (α, β) ∈ GL(A) × Aut(Q) and
b ∈ C1(Q, A). A pair satisfying (9.5) is compatible. Its induced map on cochains is
(Tα,βf)(q1, . . . , qj) = αf(β−1q1, . . . , β−1qj). It commutes with the differentials, and (9.6) is
solvable exactly when [Tα,βfG] = [fH]."

Let `p` be prime, `A = F_p^a`, `Q` a finite group, `θ_G, θ_H` actions of `Q` on `A` with normalised
2-cocycles `f_G, f_H`, and `(α, β) ∈ GL(A) × Aut(Q)`.
1. For every `b : Q → A`, the map `F(u, q) = (αu + b(q), βq)` is a group isomorphism
   `Ext θ_G f_G ≃* Ext θ_H f_H` if and only if (9.5) and (9.6) hold for all `q, r`.
2. If (9.5) holds, `T_{α,β}` commutes with the differentials in every degree.
3. If (9.5) holds, (9.6) has a solution `b` if and only if `T_{α,β} f_G − f_H` is a coboundary for
   `θ_H`, i.e. `[T_{α,β} f_G] = [f_H]` in `H²(Q, A)`.

**Formalization Note.** `F` is required to be (the underlying map of) a multiplicative bijection; the
classes in `H²` are compared by asking that the difference of the cocycles be `d b'` for a 1-cochain
`b'`. -/
theorem extension_iso_criterion {p a : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (θG θH : Representation (ZMod p) Q (Fin a → ZMod p)) (fG : NormCocycle θG) (fH : NormCocycle θH)
    (α : (Fin a → ZMod p) ≃ₗ[ZMod p] (Fin a → ZMod p)) (β : MulAut Q) :
    (∀ b : Q → (Fin a → ZMod p),
      (∃ F : Ext θG fG ≃* Ext θH fH, ∀ (u : Fin a → ZMod p) (q : Q),
          F (Ext.mk u q) = Ext.mk (α u + b q) (β q)) ↔
        ((∀ (q : Q) (v : Fin a → ZMod p), α (θG q v) = θH (β q) (α v)) ∧
          ∀ q r : Q, b q + θH (β q) (b r) - b (q * r) = α (fG.f q r) - fH.f (β q) (β r))) ∧
    ((∀ (q : Q) (v : Fin a → ZMod p), α (θG q v) = θH (β q) (α v)) →
      (∀ (j : ℕ) (f : (Fin j → Q) → (Fin a → ZMod p)),
          Tmap α β (j + 1) (coboundary θG j f) = coboundary θH j (Tmap α β j f)) ∧
        ((∃ b : Q → (Fin a → ZMod p),
            ∀ q r : Q, b q + θH (β q) (b r) - b (q * r) = α (fG.f q r) - fH.f (β q) (β r)) ↔
          ∃ c : (Fin 1 → Q) → (Fin a → ZMod p),
            coboundary θH 1 c =
              fun g => Tmap α β 2 (fun x => fG.f (x 0) (x 1)) g - fH.f (g 0) (g 1))) := by sorry

end GroupIsoPoly
