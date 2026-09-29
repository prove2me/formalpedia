-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact
-- name    : NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/4dedd3be-801e-5953-b2d8-b77321af476a
-- title:
--   Uniform convergence and decay of an adelic theta series
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and let $\Phi \colon \mathbb{A}_F^2 \to \mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the functions of the form $x \mapsto g((x_i)_{\infty})\, h((x_i)_{\text{fin}})$ with $g$ a Schwartz function on $(\mathrm{mixedSpace}\,F)^2$ (the infinite adelic components being transported to the mixed space) and $h$ a locally constant, compactly supported function of the two finite-adelic components. Let $K$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and let $N$ be a natural number. The assertion is the existence of a real constant $C \ge 0$ such that for every $m \in K$, every $x \in \mathbb{A}_F$ and all ideles $a, b \in \mathbb{A}_F^\times$ whose finite-adelic components equal $1$, the family indexed by $\xi \in F^2$ of the numbers $\bigl\|\Phi\bigl((a\,\xi_0,\ b\,(\xi_0 x + \xi_1))\, m\bigr)\bigr\|$ — the row vector $(a\xi_0, b(\xi_0x+\xi_1))$, with $\xi_i \in F$ mapped into $\mathbb{A}_F$, multiplied on the right by the matrix underlying $m$ — is summable, and its sum over $\xi \ne 0$ satisfies $$\sum_{\xi \ne 0} \bigl\|\Phi\bigl((a\xi_0, b(\xi_0x+\xi_1))m\bigr)\bigr\| \le C\bigl(1 + \|a\|^{-2}\bigr)\bigl(1+\|b\|^{-2}\bigr)\bigl(\min(1,\|a\|^{-N}) + \min(1,\|b\|^{-N})\bigr),$$ where $\|\cdot\|$ is `ideleNorm F`, the value of the distributive Haar character of $\mathbb{A}_F$ at the idele, viewed as a real number.
--
--   This is the theta-series estimate underlying Tate's method for the $\mathrm{GL}_2$ Eisenstein series attached to a Godement section: the sum over $\xi \in F^2 \setminus \{0\}$ of $\Phi(\xi\, n(x)\,\mathrm{diag}(a,b)\,m)$ is shown to converge absolutely, uniformly for $m$ in a compact set and uniformly in the shear parameter $x$, with decay in the idelic norms of the two diagonal entries controlled to order $N$. It is used in the integral estimates for the windowed Siegel sets that produce the analytic continuation of the adelic zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact.lean

import Definitions.Def_AutomorphicForm_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm

theorem NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (K : Set (AdelicGL2 (𝓞 F) F)) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 F) F) (a b : (AdeleRing (𝓞 F) F)ˣ),
        (a : AdeleRing (𝓞 F) F).2 = 1 → (b : AdeleRing (𝓞 F) F).2 = 1 →
        Summable (fun ξ : Fin 2 → F =>
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) (ξ 0),
                (b : AdeleRing (𝓞 F) F) *
                  (algebraMap F (AdeleRing (𝓞 F) F) (ξ 0) * x + algebraMap F (AdeleRing (𝓞 F) F) (ξ 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 0),
                (b : AdeleRing (𝓞 F) F) *
                  (algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 0) * x + algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖
          ≤ C * (1 + (ideleNorm F a)⁻¹ ^ 2) * (1 + (ideleNorm F b)⁻¹ ^ 2)
              * (min 1 ((ideleNorm F a)⁻¹ ^ N) + min 1 ((ideleNorm F b)⁻¹ ^ N)) := by sorry
