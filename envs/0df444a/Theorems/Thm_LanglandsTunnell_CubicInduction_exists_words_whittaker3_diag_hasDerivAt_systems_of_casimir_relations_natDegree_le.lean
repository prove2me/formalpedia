-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
-- name    : LanglandsTunnell.CubicInduction.exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/5434fcce-d69f-521b-a3b8-a557b734908f
-- title:
--   Regular-singular diagonal systems for GL₃ Whittaker coefficients
-- statement:
--   For all natural numbers $N_2,N_3$ there exist natural numbers $d,d_2,d',d_2'$ with the following property. Let $\omega$ be a homomorphism from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$, and let $a_2:\mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3:\mathrm{Fin}(N_3+1)\to\mathbb{C}$ have last entries $1$. Then there are finite sets $\iota,\iota'\subset\mathbb{C}$ and nonzero $q,q'\in\mathbb{C}[X]$, each of degree at most $6N_2N_3+1$, every root of $q$ (resp. $q'$) being of the form $e_0+j$ with $e_0\in\iota$ (resp. $\iota'$) and $j\in\mathbb{N}$, such that for every $u:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfying: all iterated archimedean right derivatives `WhittakerBlock.archDeriv` $i,j$ of $u$ along words in $\mathrm{Fin}\,3\times\mathrm{Fin}\,3$ are continuous; $u$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$; $u(zg)=\omega(z)u(g)$ for central adelic scalars $z$; [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on $\{\det\neq0\}$ for each $g$; the right translates $g\mapsto u(gk)$, for $k$ trivial at every finite place and with archimedean component in `orth3` $=\{k:k^{\mathsf T}k=1\}$, all lie in the span of one finite set of functions; and the two relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$, $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\partial_{ij}\partial_{ji}\varphi$ and $\mathrm{casimir3}\,\varphi=\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}\varphi$ in these derivatives — there exist $r\in\mathbb{N}$, words $w:\mathrm{Fin}(r+1)\to\mathrm{List}(\mathrm{Fin}\,3\times\mathrm{Fin}\,3)$, elements $\kappa:\mathrm{Fin}(r+1)\to\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, continuous matrix families $Mc\,g\,b$ ($b\in\mathrm{Fin}(d_2+1)$) and $Mc'\,g\,a$ ($a\in\mathrm{Fin}(d_2'+1)$) of size $r+1$, and continuous families of continuous linear operators $A\,g\,k\,b$ ($k\in\mathrm{Fin}\,d$), $A'\,g\,k\,a$ ($k\in\mathrm{Fin}\,d'$) on $\mathrm{Fin}(r+1)\to\mathbb{C}$, with $w\,0=[\,]$, $\kappa\,0=1$, and every $\kappa i$ trivial at all finite places with archimedean component in `orth3`, such that for every $g_0$ whose archimedean component lies in `orth3`: $q$ annihilates $\sum_b z^b\,Mc\,g_0\,b$ for all real $z>0$, $q'$ annihilates $\sum_a y^a\,Mc'\,g_0\,a$ for all $y>0$, and every $F:\mathbb{R}\times\mathbb{R}\to(\mathrm{Fin}(r+1)\to\mathbb{C})$ whose $i$-th entry is the Whittaker integral `whittaker3` (the triple integral over the upper unipotent variables against `psiQ`$(-(x+y))$ for the conditional adelic measure attached to `AdelicBox.adelicBox`) of the $w(i)$-derivative of $u$ at $\mathrm{archRealLift3}\,\mathrm{diag}(yz,z,1)\cdot g_0\cdot\kappa i$ satisfies: its $0$-th entry is the Whittaker integral of $u$ at $\mathrm{archRealLift3}\,\mathrm{diag}(yz,z,1)\cdot g_0$, and there are $Fy,Fz$ with, for $y,z>0$, $y\mapsto F\,y\,z$ differentiable with derivative $Fy\,y\,z$ and $y\,Fy\,y\,z=\bigl(\sum_b z^b Mc\,g_0\,b\bigr)F\,y\,z+\sum_{k<d}\sum_b y^{k+1}z^{b}\,A\,g_0\,k\,b(F\,y\,z)$, and symmetrically $z\mapsto F\,y\,z$ differentiable with derivative $Fz\,y\,z$ and $z\,Fz\,y\,z=\bigl(\sum_a y^a Mc'\,g_0\,a\bigr)F\,y\,z+\sum_{k<d'}\sum_a z^{k+1}y^{a}\,A'\,g_0\,k\,a(F\,y\,z)$.
--
--   This packages the Whittaker coefficient of an automorphic function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, restricted to the diagonal torus $\mathrm{diag}(yz,z,1)$ and to a finite vector of derivative translates, as a solution of two commuting first-order systems with singularity of the first kind at $y=0$ and at $z=0$, the residue matrices being annihilated by polynomials whose roots lie in finitely many arithmetic progressions of exponents. It is the input for the subsequent extraction of exponents and asymptotic expansions of Whittaker coefficients in the cubic induction, being cited by the results on expansions along the torus and on the leading coefficient of the regular-singular system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
    (N₂ N₃ : ℕ) :
    ∃ (d d₂ d' d₂' : ℕ),
      ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 →
      ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
      ∃ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ 6 * N₂ * N₃ + 1 ∧ q'.natDegree ≤ 6 * N₂ * N₃ + 1 ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j) ∧
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z)) := by sorry
