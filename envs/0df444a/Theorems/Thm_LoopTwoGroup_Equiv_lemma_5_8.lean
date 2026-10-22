-- Prove2me | Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_8
-- name    : LoopTwoGroup.Equiv.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:50.520986+00:00
-- url     : https://prove2.me/theorems/57ab70ed-090f-43ba-83f7-2b8d288412bb
-- title:
--   Lemma 5.8 — φψ is the identity and ψφ is 2-isomorphic to the identity
-- statement:
--   Let $\phi$ and $\psi$ have the displayed components of Lemmas 5.4 and 5.7 for a smooth $f$ with $f(0)=0$ and $f(2\pi)=1$. Then
--   $$(\phi\circ\psi)_0=\mathrm{id},\qquad (\phi\circ\psi)_1=\mathrm{id},\qquad (\phi\circ\psi)_2=0,$$
--   and $\psi\circ\phi$ is 2-isomorphic to the identity on $\mathcal P_k\mathfrak g$. The 2-homomorphism $\tau:\psi\circ\phi\Rightarrow\mathrm{id}$ has
--   $$\tau(p)=\bigl(p-p(2\pi)f,0\bigr).$$
--   This supplies the inverse-up-to-isomorphism condition for the quotient map of Theorem 5.1.
--
--   **Formalization Note** Composition is the component formula (6), and a 2-homomorphism carries both chain-homotopy equations and equation (7). The theorem existentially supplies $\phi$ and $\psi$ with their components.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, pp. 33–34, Lemma 5.8 and the display defining τ on p. 33

import Mathlib
import Definitions.Def_LoopTwoGroup_Equiv_Model

namespace LoopTwoGroup.Equiv

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

/-- Lemma 5.8, pp. 33–34: `φ ∘ ψ` is the identity and `ψ ∘ φ`
is 2-isomorphic to the identity by the displayed `τ`. -/
theorem lemma_5_8 (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) :
    ∃ (Φ : LInfHom (Pk L k) (gk L k)) (Ψ : LInfHom (gk L k) (Pk L k)),
      PhiComponents L k Φ ∧ PsiComponents L k f Ψ ∧
      compF0 Ψ Φ = LinearMap.id ∧ compF1 Ψ Φ = LinearMap.id ∧
      (∀ a b, compF2 Ψ Φ a b = 0) ∧
      ∃ T : TwoHom (Pk L k) (Pk L k)
        (compF0 Φ Ψ) LinearMap.id (compF1 Φ Ψ) LinearMap.id
        (compF2 Φ Ψ) (fun _ _ => 0),
        (∀ p t, ((T.τ p).1).1 t = p.1 t - f (clamp t) • p.1 (2 * Real.pi)) ∧
        (∀ p, (T.τ p).2 = 0) := by sorry

end LoopTwoGroup.Equiv
