-- Prove2me | Theorems.Thm_MTT_Eigenform_exists_frickeRootNumber_quadratic_twist
-- name    : MTT.Eigenform.exists_frickeRootNumber_quadratic_twist
-- status  : Open
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:02:10.897982+00:00
-- url     : https://prove2.me/theorems/fe2311a6-337a-4be0-9472-706660d9b803
-- title:
--   Fricke root number and coprime quadratic twisting for primitive eigenforms
-- statement:
--   Let $N>0$ and let $k\ge2$ be even. Let $f$ be a normalized algebraic cuspidal Hecke eigenform, with a fixed complex coefficient embedding, at the least positive level $N$ in its Hecke system. There is a complex number $w$ with $|w|=1$ such that
--
--   $$f\!\left(\frac{i}{Nt}\right)=wN^{k/2}t^k\overline{f(it)}\qquad(t>0).$$
--
--   If all the embedded Fourier coefficients of $f$ are real, then $w\in\{1,-1\}$. For every primitive quadratic Dirichlet character $\eta$ of modulus $m$ coprime to $N$, put $F=f_{\eta^{-1}}$, using the finite-translate twist. Then
--
--   $$F\!\left(\frac{i}{Nm^2t}\right)=w\varepsilon_f(m)\eta(-N)(Nm^2)^{k/2}t^k\overline{F(it)}\qquad(t>0).$$
--
--   This identifies the genuine functional-equation scalar of a coprime quadratic twist. It asserts no nonvanishing of central values.
--
--   **Formalization Note.** The functions in these identities are the actual cusp form and the mission's `MTT.inverseTwist`, not unspecified associated forms. Minimality is with respect to the current weight, and the nebentype is unrestricted. The primitive-newform identification and the analytic Fricke identities remain obligations of this open theorem.
-- source:
--   Atkin--Li, Twists of newforms and pseudo-eigenvalues of W-operators, Invent. Math. 48 (1978), 221--243, especially the coprime twisting formula on p.228, https://doi.org/10.1007/BF01390245. Exact twist formula inspected in Nicolas Mascot's thesis, Theorem A.2.2.34, printed p.82, https://warwick.ac.uk/fac/sci/maths/people/staff/mascot/these.pdf. Independent unconditional twisting identity: Bettin et al., A conjectural extension of Hecke's converse theorem, equation (1.8), p.2, and Lemma 4.10, p.15, https://arxiv.org/pdf/1704.02570. Quadraticity cancels the Gauss-sum ratio. The displayed pointwise normalization is obtained at z=it, with w=i^k times the usual Fricke pseudo-eigenvalue. Minimal-level identification uses Atkin--Lehner--Li theory, Stein Chapter 9, Theorem 9.4, https://wstein.org/books/modform/modform/newforms.html.

import Definitions.Def_MTT_QuadraticTwistRootNumber

set_option autoImplicit false

open HorizontalPadicL

/-- The primitive eigenform Fricke equation and its coprime quadratic twist law. -/
theorem MTT.Eigenform.exists_frickeRootNumber_quadratic_twist
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (hmin : f.HasMinimalLevel) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ MTT.HasFrickeRootNumber f.form N k w ∧
      (f.HasRealCoefficients → w = 1 ∨ w = -1) ∧
      ∀ (η : DirichletCharacterWithLevel), η.2.IsPrimitive → orderOf η.2 = 2 →
        Nat.Coprime N η.1.1 →
        MTT.HasFrickeRootNumber
          (@MTT.inverseTwist ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2)
          (N * η.1.1 ^ 2) k (w * ι (f.epsilon η.1.1) * ι (η.2 (-N))) := by
  sorry
