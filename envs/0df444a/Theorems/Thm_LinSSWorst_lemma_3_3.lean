-- Prove2me | Theorems.Thm_LinSSWorst_lemma_3_3
-- name    : LinSSWorst.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:05:12.00004+00:00
-- url     : https://prove2.me/theorems/054b9b90-ce41-4efa-8791-547a33b75671
-- title:
--   Lemma 3.3 (Common-pad privacy) — a view of the form $(N\rho_1, a(s+\omega)+M\rho_2)$ does not depend on $s$
-- statement:
--   Let $F$ be a finite field. Let $\omega$ be uniform on $F$, let $(\rho_1,\rho_2)\in F^{r_1}\times F^{r_2}$ be a pair of random vectors with an arbitrary joint law, independent of $\omega$, and let $N\in F^{m_0\times r_1}$, $M\in F^{m_1\times r_2}$ and $a\in F^{m_1}$. Suppose that a family of distributions $\mathrm{View}_B(s)$ on $F^{m_0}\times F^{m_1}$, indexed by the secret $s\in F$, satisfies, for every $s\in F$,
--   $$\mathrm{View}_B(s)\overset{d}{=}\big(N\rho_1,\ a(s+\omega)+M\rho_2\big).$$
--   Then $\mathrm{View}_B(s_0)=\mathrm{View}_B(s_1)$ for all $s_0,s_1\in F$.
--
--   The lemma reduces the privacy of Construction 3.1 to exhibiting a single pad that masks the secret in every visible linear combination.
--
--   **Formalization Note** The joint law of $(\omega,\rho_1,\rho_2)$ is the uniform law on $F$ bound with an arbitrary PMF $\mu$ of $(\rho_1,\rho_2)$; $\rho_1$ and $\rho_2$ need not be uniform or independent of each other.
--
--   Differences from the source:
--   - generalization: View_B(s), the view of a coalition B under a linear share-distribution procedure Π → any family View : F → PMF (F^{m₀} × F^{m₁}); reason: the linearity of Π is not used; the views of the source are such a family, so the Lean statement specializes to the source's
--   - encoding: ω uniform, ρ₁ ∈ F^{r₁}, ρ₂ ∈ F^{r₂} random, ω independent of (ρ₁, ρ₂) → joint law `(uniformOfFintype F).bind (fun ω => μ.map (ω, ·))` with μ an arbitrary PMF of (ρ₁, ρ₂); reason: this is exactly the law of such a triple
--   - encoding: "the distribution of View_B(s) is independent of s" → View s₀ = View s₁ for all s₀, s₁; reason: same statement
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Lemma 3.3, p.13

import Mathlib

open Matrix

namespace LinSSWorst

/-- **Lemma 3.3 (Common-pad privacy)**, p.13, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…).
Let `ω` be a uniform pad in `F`, let `(ρ_1, ρ_2) ∈ F^{r_1} × F^{r_2}` have any joint law `μ`, with
`ω` independent of `(ρ_1, ρ_2)`, and let `N ∈ F^{m_0×r_1}`, `M ∈ F^{m_1×r_2}`, `a ∈ F^{m_1}`. If the
view `View_B(s)` has, for every secret `s ∈ F`, the law of `(Nρ_1, a(s + ω) + Mρ_2)`, then the
law of `View_B(s)` does not depend on `s`.

**Formalization Note.** The joint law of `(ω, ρ_1, ρ_2)` is the uniform law on `F` bound with the
arbitrary PMF `μ` (independence, with `ω` uniform); `ρ_1` and `ρ_2` need not be uniform or
independent of each other. `View` is any family of PMFs on `F^{m_0} × F^{m_1}`: the "linear
share-distribution procedure" of the page plays no role and is not modelled. The hypothesis is
equality in distribution for every `s`; the conclusion is `View s₀ = View s₁` for all `s₀, s₁`. -/
theorem lemma_3_3 {F : Type*} [Field F] [Fintype F] {r₁ r₂ m₀ m₁ : ℕ}
    (μ : PMF ((Fin r₁ → F) × (Fin r₂ → F)))
    (N : Matrix (Fin m₀) (Fin r₁) F) (M : Matrix (Fin m₁) (Fin r₂) F) (a : Fin m₁ → F)
    (View : F → PMF ((Fin m₀ → F) × (Fin m₁ → F)))
    (hView : ∀ s : F, View s =
      ((PMF.uniformOfFintype F).bind fun ω => μ.map fun ρ => (ω, ρ)).map
        (fun t => (N *ᵥ t.2.1, (s + t.1) • a + M *ᵥ t.2.2))) :
    ∀ s₀ s₁ : F, View s₀ = View s₁ := by sorry

end LinSSWorst
