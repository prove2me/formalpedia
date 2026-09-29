-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
-- name    : LanglandsTunnell.CubicInduction.exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/14304f5b-ea77-5a06-9d77-613419e1c9d6
-- title:
--   Universal torus table for GL₃ Whittaker coefficients
-- statement:
--   Let $S$ be a finite set of finite places of $\mathbb{Q}$ (height one primes of $\mathcal{O}_{\mathbb{Q}}$), let $\omega$ be a group homomorphism from the ideles $\mathbb{A}_{\mathbb{Q}}^{\times}$ to $\mathbb{C}^{\times}$ (no continuity assumed), let $\lambda_1,\lambda_2$ be arbitrary complex-valued functions on the finite places, and let $p\notin S$ be a finite place. The assertion is the existence of a single function $u:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$, depending only on these data, with $u(0,0)=1$ and $u(m)=0$ unless $0\le m_2\le m_1$, such that the following holds for every $f:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ that is continuous, satisfies $f(\gamma g)=f(g)$ for $\gamma\in\mathrm{GL}_3(\mathbb{Q})$ embedded by `globalPointsGL` and $f(zg)=\omega(z)f(g)$ for ideles $z$ embedded as central scalars, and, at every place $q\notin S$, is right invariant under the image in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ of `localMaximalCompact3` at $q$ (those $k\in\mathrm{GL}_3(\mathbb{Q}_q)$ all of whose entries and whose inverse's entries have valuation $\le 1$) and satisfies `IsCosetEigenfunction` for the local elements $\mathrm{diag}(\varpi_q,1,1)$ and $\mathrm{diag}(\varpi_q,\varpi_q,1)$ with eigenvalues $\lambda_1(q)$, $\lambda_2(q)$, i.e. for every finite system of representatives forming a Hecke coset system for that compact subgroup and that element, the corresponding coset sum of $f$ equals the eigenvalue times $f$ everywhere: for every $g_0\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ commuting with the entire local image of $\mathrm{GL}_3(\mathbb{Q}_p)$ and every $m\in\mathbb{Z}\times\mathbb{Z}$, the Whittaker coefficient `whittaker3` of $f$ — the triple integral of $f(n(x,y,z)g)\,\psi_{\mathbb{Q}}(-(x+y))$ over upper unipotent matrices, the variables running over the adeles with the additive Haar measure conditioned on the adelic box (infinite box times integral finite adeles) — evaluated at $g_0$ times the local image of the block embedding into $\mathrm{GL}_3$ of $\mathrm{diag}(\pi_p^{m_1},\pi_p^{m_2})$, where $\pi_p$ is `ratPrimeUnit` at $p$, equals its value at $g_0$ multiplied by $u(m)$.
--
--   This is the adelic form of the unramified (class one) Whittaker function computation of Shintani and Casselman–Shalika for $\mathrm{GL}_3$: along the torus at a good place the Whittaker coefficient is the base-point value times a table depending only on the Hecke eigenvalues, supported on dominant weights. It feeds the slab and smoothing-operator estimates used later in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm NumberField.StandardAddChar

theorem LanglandsTunnell.CubicInduction.exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S) :
    ∃ u : ℤ × ℤ → ℂ, u (0, 0) = 1 ∧ (∀ m : ℤ × ℤ, ¬ (0 ≤ m.2 ∧ m.2 ≤ m.1) → u m = 0) ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
        (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
        (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
          f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
        (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
        (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
        (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
        (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (_hg₀ : ∀ x : LocalGL3 p, g₀ * localToAdelic3 p x = localToAdelic3 p x * g₀)
        (m : ℤ × ℤ),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f
            (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g₀ *
            u m := by sorry
