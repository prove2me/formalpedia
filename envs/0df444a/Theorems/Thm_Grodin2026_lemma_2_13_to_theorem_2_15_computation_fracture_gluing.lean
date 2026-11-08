-- Prove2me | Theorems.Thm_Grodin2026_lemma_2_13_to_theorem_2_15_computation_fracture_gluing
-- name    : Grodin2026.lemma_2_13_to_theorem_2_15_computation_fracture_gluing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:18:13.944427+00:00
-- url     : https://prove2.me/theorems/96c83710-0f9f-4dab-9c7e-a73ccc945965
-- title:
--   Lemmas 2.13–2.14, Theorem 2.15, Corollaries 2.16 & 2.18, and Lemma 2.19: Fracture and Gluing of Computation Types
-- statement:
--   Proves compatibility of the underlying-value functor $U$ with $\bigcirc$ and $\bullet$ ($U(\bigcirc A) = \bigcirc(UA)$ and $U(\bullet A) = \bullet(UA)$, Lemma 2.13), lex pullback preservation for $\bigcirc$ and $\bullet$ on $\mathcal{C}$ (Lemma 2.14), the fracture and gluing equivalence $A \simeq \mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)$ on computation types together with modal recovery of $\bullet A$ and $\bigcirc A$ (Theorem 2.15), the equivalence $\mathsf{GlueAbstractionComp}\,A_\top\,A_{\mathsf{abs}}\,\alpha \simeq \mathsf{AbstractionComp}\,A_\top\,A_{\mathsf{abs}}\,\alpha$ (Definition 2.17) and $C_0 \simeq \mathsf{GlueAbstractionComp}\,C_0\,C_0\,\mathrm{id}_{C_0}$ (Corollary 2.18), and modal coherence for computation homomorphisms (Corollary 2.16, Lemma 2.19).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Section 2.2, Lemmas 2.13-2.14, Theorem 2.15, Corollaries 2.16 & 2.18, Lemma 2.19, pp. 7-10.

import Definitions.Def_Grodin2026_Physicist

namespace Grodin2026

/-- **Lemma 2.13, Lemma 2.14, Theorem 2.15, Corollary 2.16, Corollary 2.18, and Lemma 2.19 (§2.2):**
1. **Underlying Value Compatibility (Lemma 2.13):** For all computation types $A : \mathcal{C}$,
   $U(\bigcirc A) = \bigcirc(UA)$ and $U(\bullet A) = \bullet(UA)$.
2. **Lex Preservation of Pullbacks (Lemma 2.14):** Both $\bigcirc$ and $\bullet$ preserve pullbacks
   in $\mathcal{C}$ up to computation equivalence (`CompEquiv`):
   $\bigcirc(A \times_C B) \simeq \bigcirc A \times_{\bigcirc C} \bigcirc B$ and
   $\bullet(A \times_C B) \simeq \bullet A \times_{\bullet C} \bullet B$.
3. **Fracture and Gluing of $\mathcal{C}$ (Theorem 2.15):** Every computation type $A : \mathcal{C}$
   is canonically equivalent (`CompEquiv`) to its pullback gluing
   $\mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)$, and fracturing the glued type
   recovers $\bullet A$ and $\bigcirc A$ up to equivalence.
4. **$\mathsf{Abstraction}$ on Computation Types (Corollary 2.16, Definition 2.17, Corollary 2.18, Lemma 2.19):**
   - For any cost algebra homomorphism $\alpha : A_\top \multimap A_{\mathsf{abs}}$,
     $\mathsf{Glue}(\bullet A_\top, \bigcirc A_{\mathsf{abs}}, \bullet(\eta^\circ \circ \alpha)) \simeq \mathsf{Abstraction}(\alpha)$;
   - For any single-world cost algebra $C_0$, $\mathsf{ConstComp}\,C_0 \simeq \mathsf{GlueAbstractionComp}\,C_0\,C_0\,\mathrm{id}_{C_0}$;
   - Every computation homomorphism $f : A \multimap B$ induces coherent $\bullet f$ and $\bigcirc f$
     satisfying $(\bullet \eta^\circ_B) \circ \bullet f = \bullet(\bigcirc f \circ \eta^\circ_A)$. -/
theorem lemma_2_13_to_theorem_2_15_computation_fracture_gluing :
    (∀ A : CompType,
      ForgetComp (OpenComp A) = OpenVal (ForgetComp A) ∧
      ForgetComp (ClosedComp A) = ClosedVal (ForgetComp A)) ∧
    (∀ {A B C : CompType} (f : CompHom A C) (g : CompHom B C),
      Nonempty (CompEquiv (OpenComp (CompPullback f g))
        (CompPullback (OpenComp.map f) (OpenComp.map g))) ∧
      Nonempty (CompEquiv (ClosedComp (CompPullback f g))
        (CompPullback (ClosedComp.map f) (ClosedComp.map g)))) ∧
    (∀ A : CompType,
      Nonempty (CompEquiv A (FractureGlueComp A)) ∧
      Nonempty (CompEquiv (ClosedComp (FractureGlueComp A)) (ClosedComp A)) ∧
      Nonempty (CompEquiv (OpenComp (FractureGlueComp A)) (OpenComp A))) ∧
    (∀ (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs),
      Nonempty (CompEquiv (GlueAbstractionComp A_top A_abs alpha)
        (AbstractionComp A_top A_abs alpha))) ∧
    (∀ C₀ : CostAlg,
      Nonempty (CompEquiv (ConstComp C₀) (GlueAbstractionComp C₀ C₀ (CostHom.id C₀)))) ∧
    (∀ {A B : CompType} (f : CompHom A B),
      (ClosedComp.map (etaOpenComp B)).comp (ClosedComp.map f) =
        ClosedComp.map ((OpenComp.map f).comp (etaOpenComp A))) := by
  sorry

end Grodin2026
