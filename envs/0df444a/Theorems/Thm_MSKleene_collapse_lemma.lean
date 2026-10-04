-- Prove2me | Theorems.Thm_MSKleene_collapse_lemma
-- name    : MSKleene.collapse_lemma
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:30:44.376428+00:00
-- url     : https://prove2.me/theorems/0525a009-0c28-49d3-b08b-7e651987950d
-- title:
--   Lemma 3.18: the collapse lemma
-- statement:
--   **The collapse lemma** (Lemma 3.18).
--
--   Let $\mathbf{A}$ be a $\Sigma$-algebra and $g$ a homomorphism from $\mathbf{T}_{\Sigma}(X)$ to $\mathbf{A}$; let $u\in S$, $z\in X_{u}$. For every $s$ and every $R\in\mathrm{T}_{\Sigma}(X)_{s}$ with $(R,s)\notin\mathrm{Min}$ there exist $P\in\mathrm{T}_{\Sigma}(X)_{s}$ and $(Q^{z}_{\alpha})_{\alpha\in|P|_{z}}$ such that: (1) $R=\left(\!\begin{smallmatrix}z\\(Q^{z}_{\alpha})\end{smallmatrix}\!\right)(P)$; (2) $g_{s}(P)=g_{s}(R)$; (3) for every $\alpha$, $(Q^{z}_{\alpha},u)<(R,s)$ and $g_{u}(Q^{z}_{\alpha})=g_{u}(z)$; (4) for every $(M,t)<(P,s)$ with $(M,t)\notin\mathrm{Min}$: (a) it is not the case that both $t=u$ and $g_{u}(M)=g_{u}(z)$, and (b) there exists $(N,t)<(R,s)$ with $(N,t)\notin\mathrm{Min}$ and $g_{t}(N)=g_{t}(M)$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_SubstFam
import Definitions.Def_MSKleene_Subterm

namespace MSKleene

/-- **The collapse lemma** (Lemma 3.18).

Let `g : T_Σ(X) → A` be a homomorphism, `z ∈ X_u`, and `R ∈ T_Σ(X)_s` a
non-minimal term. Then there are a term `P` and a family `qs` for the
occurrences of `z` in `P` such that:
1. `R = ⟨z/qs⟩(P)`;
2. `g_s(P) = g_s(R)`;
3. every `qs α` is a proper subterm of `R` with `g_u(qs α) = g_u(z)`;
4. every proper non-minimal subterm `M` of `P` (a) does not have both sort `u`
   and `g`-image `g_u(z)`, and (b) has a proper non-minimal subterm `N` of `R`
   of the same sort with `g(N) = g(M)`. -/
theorem collapse_lemma {S : Type} (sig : Signature S) (X : SSet S)
    (A : Algebra sig) (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) {s : S}
    (R : Term sig X s) (hR : ¬ Min (⟨s, R⟩ : STerm sig X)) :
    ∃ (P : Term sig X s) (qs : Fin (Term.occ z P) → Term sig X u),
      R = substFam z P qs
    ∧ g.toFun s P = g.toFun s R
    ∧ (∀ α, SubtermLT (⟨u, qs α⟩ : STerm sig X) ⟨s, R⟩
            ∧ g.toFun u (qs α) = g.toFun u (Term.var z))
    ∧ (∀ M : STerm sig X, SubtermLT M ⟨s, P⟩ → ¬ Min M →
        (¬ ∃ h : M.1 = u, g.toFun u (h ▸ M.2) = g.toFun u (Term.var z))
        ∧ (∃ N : STerm sig X, SubtermLT N ⟨s, R⟩ ∧ ¬ Min N
            ∧ ∃ h : N.1 = M.1, g.toFun M.1 (h ▸ N.2) = g.toFun M.1 M.2)) := by
  sorry

end MSKleene
