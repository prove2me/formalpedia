-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_family_read_of_actStable_signIsotypic
-- name    : LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ab97ef88-a2ad-5c48-965a-59873fca417b
-- title:
--   Transition-stable family read in a sign-isotypic polynomial space
-- statement:
--   Fix $\nu \in \mathbb{C}^3$, a sign vector $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and a $\mathbb{C}$-submodule $W$ of the polynomial ring in the nine variables $X_{(a,c)}$, $a,c \in \mathrm{Fin}\,3$. Four operators are introduced inside the statement: $\mathrm{act}\,\nu\,c\,d$, the first-order operator sending $P$ to $\bigl(\sum_a (\nu_a + (1,0,-1)_a) X_{(a,c)}X_{(a,d)}\bigr)P$ plus $\sum_{i,j}\bigl(\sum_m \epsilon_{im}(c,d)\,X_{(m,j)}\bigr)\partial_{(i,j)}P$, where $\epsilon_{im}(c,d)$ is $X_{(i,c)}X_{(m,d)}$ for $m<i$, $-X_{(m,c)}X_{(i,d)}$ for $i<m$ and $0$ for $m=i$; the matrix $\Xi\,\nu\,p$ over $\mathbb{C}[x_0,x_1,x_2]$ with diagonal entries $2(\nu_c + (1,0,-1)_c)p$ and off-diagonal entries $-\bigl(x_{\max(c,d)}\partial_{\min(c,d)}p - x_{\min(c,d)}\partial_{\max(c,d)}p\bigr)$; and the contractions $\mathrm{lower}_2(M) = \sum_{c,d}\partial_c\partial_d M_{cd}$ and $\mathrm{lower}_1(M) = \sum_{a,b,c,d} \tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\,\partial_b\partial_d M_{ab}$ (indices read as natural numbers in $\mathbb{C}$). Assume: $W$ is stable under every $\mathrm{act}\,\nu\,c\,d$; $W$ is stable under the substitution $X_{(i,j)} \mapsto \sum_c X_{(i,c)}\,r_{cj}$ for every real $3\times 3$ matrix $r$ with $\sum_a r_{ai}r_{aj} = \delta_{ij}$; and $W$ is $\varepsilon$-isotypic for left sign changes, i.e. for $P \in W$, $\tau : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and every such orthogonal $o$, the value of $P$ at the matrix $\mathrm{diag}((-1)^{\tau_a})\,o$ equals $(-1)^{\sum_a \varepsilon_a \tau_a}$ times its value at $o$. Say that $p \in \mathbb{C}[x_0,x_1,x_2]$ is read in $W$ at degree $\ell$ if there is $Q \in W$ with $Q(o) = \det(o)^{(\ell + \sum_a \varepsilon_a) \bmod 2}\, p(o_{00},o_{10},o_{20})$ for all orthogonal $o$ as above. The conclusion is the existence of a family $S : \mathbb{N} \to$ submodules of $\mathbb{C}[x_0,x_1,x_2]$ such that: every $p \in S\,\ell$ is homogeneous of degree $\ell$ and harmonic ($\sum_i \partial_i^2 p = 0$); every $p \in S\,\ell$ satisfies $p((-1)^{\sigma_a}x_a) = (-1)^{\sum_a (\varepsilon_a + \ell + \sum_b \varepsilon_b)\sigma_a}\,p$ for all $\sigma : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$; $\mathrm{lower}_2(\Xi\,\nu\,p) \in S(\ell-2)$ and $\mathrm{lower}_1(\Xi\,\nu\,p) \in S(\ell-1)$ for $p \in S\,\ell$ (truncated subtraction); every $p \in S\,\ell$ is read in $W$ at degree $\ell$; conversely every homogeneous harmonic $p$ of degree $\ell$ read in $W$ at degree $\ell$ lies in $S\,\ell$; and if some $P \in W$ has nonzero value at some orthogonal $o$, then $S\,\ell \neq \bot$ for some $\ell$.
--
--   This packages the harmonic polynomials of each degree that are read off from $W$ by the determinant-twisted restriction to the first column of an orthogonal matrix into a family stable under the two lowering contractions of the compact-picture matrix $\Xi\,\nu$, together with its sign type and a non-vanishing criterion; it is the polynomial-model form of the transition-and-exhaustion mechanism used in the Langlands–Tunnell step. It is cited in the derivation of a member of $W$ whose values on the orthogonal group realise the determinant-twisted read-out in the odd sign class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_family_read_of_actStable_signIsotypic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ)) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    ∃ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
            (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
              MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p))) ∧
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
        (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 →
        (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
            (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
              MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) → p ∈ S ℓ) ∧
      ((∃ P ∈ W, ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → ∃ ℓ, S ℓ ≠ ⊥) := by sorry
