-- Prove2me | Theorems.Thm_IntLInfty_Kan_generator_lift_dga
-- name    : IntLInfty.Kan.generator_lift_dga
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:45.258366+00:00
-- url     : https://prove2.me/theorems/e4583306-9c78-4cd4-8cf7-ee710864b6be
-- title:
--   Algebra maps out of the Chevalley-Eilenberg algebra are determined by generator values, and the DGA condition reduces to generators (Henriques, Thm 5.10 proof)
-- statement:
--   Nine facts about the Chevalley-Eilenberg algebra $C^*(L)$ and differential forms on $\Delta^m$.
--   (1) Every family of linear maps $f_i : L_i^* \to \Omega(\Delta^m)$ whose values are pointwise of degree $i+1$ extends to an algebra map $$\Phi : C^*(L) \to \Omega(\Delta^m),\qquad \Phi(\xi) = f_i(\xi)\quad(\xi \in L_i^*)$$ (graded commutativity of forms).
--   (2) If an algebra map $\Phi$ sends the generators of a generator system $S$ to $C^r$ forms of the right degree with $d\Phi(\xi) = \Phi(\delta\xi)$ on $\Delta^m$ ($r\ge 1$), then every $a \in A_S$ has $\Phi(a)$ of class $C^r$ and $d\Phi(a) = \Phi(\delta a)$ on $\Delta^m$; (3) hence $\Phi|_{A_S}$ is a DGA map in the sense of IsDGAMap.
--   (4)-(6) Leibniz rule $d(\alpha\wedge\beta) = d\alpha\wedge\beta + (-1)^p\alpha\wedge d\beta$ for a $p$-form $\alpha$, products of $C^r$ forms are $C^r$, degrees add. (7) Constant forms are $C^r$ and closed. (8) $\delta(1) = 0$. (9) $C^r$-regularity only depends on the values on $\Delta^m$.
--
--   Role: library node of the proof of Theorem 5.10 (integration of the Postnikov tower): every point of $\int_S$ is built as the restriction of such a lift.
-- source:
--   A. Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563, https://arxiv.org/abs/math/0603563, Section 5, Definition 5.2 and proof of Theorem 5.10

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

namespace IntLInfty.Kan

theorem generator_lift_dga :
    (∀ {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)]
      (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ),
        f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))) →
      ∃ Φ : CE L →ₐ[ℝ] Ω m, ∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), Φ (gen L i ξ) = f i ξ) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)], 1 ≤ r →
      ∀ (δ : LInfty L) (S : GenSys L) (Φ : CE L →ₐ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsDeg (i + 1) (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsCr r (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        ∀ x ∈ simplex m, extD (Φ (gen L i ξ)) x = Φ (δ.δ (gen L i ξ)) x) →
      ∀ a ∈ genAlg L S, IsCr r (Φ a) ∧ ∀ x ∈ simplex m, extD (Φ a) x = Φ (δ.δ a) x) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)], 1 ≤ r →
      ∀ (δ : LInfty L) (S : GenSys L) (Φ : CE L →ₐ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsDeg (i + 1) (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsCr r (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        ∀ x ∈ simplex m, extD (Φ (gen L i ξ)) x = Φ (δ.δ (gen L i ξ)) x) →
      IsDGAMap r δ S m (Φ.comp (genAlg L S).val)) ∧
    (∀ {m r p : ℕ}, 1 ≤ r → ∀ {α β : Ω m}, IsCr r α → IsCr r β → IsDeg p α →
      ∀ x ∈ simplex m, extD (α * β) x = extD α x * β x + (-1 : ℝ) ^ p • (α x * extD β x)) ∧
    (∀ {m r p : ℕ}, 1 ≤ r → ∀ {α β : Ω m}, IsCr r α → IsCr r β → IsDeg p α → IsCr r (α * β)) ∧
    (∀ {m p q : ℕ} {α β : Ω m}, IsDeg p α → IsDeg q β → IsDeg (p + q) (α * β)) ∧
    (∀ {m : ℕ} (r : ℕ) (a : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))),
      IsCr r (fun _ => a : Ω m) ∧ extD (fun _ => a : Ω m) = 0) ∧
    (∀ {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] (δ : LInfty L),
      δ.δ 1 = 0) ∧
    (∀ {m r : ℕ} {ω ω' : Ω m}, (∀ x ∈ simplex m, ω x = ω' x) → IsCr r ω → IsCr r ω') := by sorry

end IntLInfty.Kan
