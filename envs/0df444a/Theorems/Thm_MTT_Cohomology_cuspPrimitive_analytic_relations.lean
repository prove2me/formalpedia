-- Prove2me | Theorems.Thm_MTT_Cohomology_cuspPrimitive_analytic_relations
-- name    : MTT.Cohomology.cuspPrimitive_analytic_relations
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T16:59:41.601617+00:00
-- url     : https://prove2.me/theorems/aca42de6-053f-420f-a034-37841b612c6e
-- title:
--   Analytic transformation and linearity of cusp primitives
-- statement:
--   Let $N>0$ and $k\ge2$. For a cusp form $f$ on $\Gamma_1(N)$, write
--
--   $$
--   F_f(r)=-2\pi i\int_r^{i\infty} f(z)(zX+Y)^{k-2}\,dz,\qquad F_f(\infty)=0.
--   $$
--
--   The cusp primitive has the following three analytic properties.
--
--   1. For $\gamma\in\Gamma_1(N)$ and every rational or infinite cusp $x$,
--      $$F_f(\gamma x)=\gamma\cdot F_f(x)+F_f(\gamma\infty).$$
--   2. For cusp forms $f,g$, one has $F_{f+g}(x)=F_f(x)+F_g(x)$.
--   3. For $a\in\mathbf C$, one has $F_{af}(x)=aF_f(x)$.
--
--   The first identity is the modular change-of-variables formula for the cusp integral. The latter identities assert linearity of the convergent improper integrals at all cusps. Together they are the analytic input needed to turn cusp-to-cusp integration into a linear, equivariant modular symbol.
-- source:
--   Shimura, Introduction to the Arithmetic Theory of Automorphic Functions (1971), Chapter 8; Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §2, construction preceding Theorem 2.3, p. 853, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.cuspPrimitive_analytic_relations
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    (∀ (f : CuspForm (MTT.GammaOne N) (k : ℤ))
        (γ : CongruenceSubgroup.Gamma1 N) (x : Cusp),
      cuspPrimitive f (cuspAct γ.val x) =
        act γ.val.val (cuspPrimitive f x) +
          cuspPrimitive f (cuspAct γ.val OnePoint.infty)) ∧
    (∀ (f g : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (f + g) x = cuspPrimitive f x + cuspPrimitive g x) ∧
    (∀ (a : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (a • f) x = a • cuspPrimitive f x) := by sorry
