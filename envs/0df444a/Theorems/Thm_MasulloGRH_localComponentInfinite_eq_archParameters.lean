-- Prove2me | Theorems.Thm_MasulloGRH_localComponentInfinite_eq_archParameters
-- name    : MasulloGRH.localComponentInfinite_eq_archParameters
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:00.297596+00:00
-- url     : https://prove2.me/theorems/358133ee-9088-43dd-a4d9-d6434cee3c03
-- title:
--   §6.3.1, p. 303 — archimedean components of a Hecke character: $\chi_w=\mathrm{sgn}^{a_w}|\cdot|_w^{it_w}$ (real $w$), $\chi_w(z)=(z/|z|)^{n}|z|_w^{it_w}$ (complex $w$), with unique parameters
-- statement:
--   **Archimedean local components of a Hecke character** (the archimedean recollection in §6.3.1 of the source, p. 303, which is the input of the Gamma factors (3.2.1.4)–(3.2.1.5)).
--
--   Let $F$ be a number field, $\chi$ a Hecke character of $F$ and $w$ an infinite place, with completion $F_w$, the embedding $\iota_w:F_w\hookrightarrow\mathbb C$ extending the embedding of $F$ that defines $w$, and the norm $\|x\|=|\iota_w(x)|$; the normalized absolute value is $|x|_w=\|x\|$ at a real place and $|x|_w=\|x\|^2$ at a complex place. Let $\chi_w:F_w^\times\to U(1)$, $\chi_w(x)=\chi(j_w(x))$, be the local component of $\chi$ at $w$, where $j_w(x)$ is the class in $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ of the idele with component $x$ at $w$ and $1$ at every other place. Let $t_w\in\mathbb R$ be the exponent with $\chi_w(x)=|x|_w^{it_w}$ for $\iota_w(x)>0$, let $a_w\in\{0,1\}$ be the parity of $\chi$ at a real place ($\chi_w(-1)=(-1)^{a_w}$), and at a complex place let $|n_w|$ be the absolute value of the weight, $\chi_w(x)=\iota_w(x)^{n_w}$ for $\|x\|=1$. Then:
--
--   1. if $w$ is real, for all $x\in F_w^\times$
--   $$\chi_w(x)=\mathrm{sgn}(x)^{a_w}\,|x|_w^{it_w},$$
--   i.e. $\chi_w|\cdot|_w^s=|\cdot|_w^{s+it_w}$ if $\chi_w$ is even and $\chi_w|\cdot|_w^s=\mathrm{sgn}\,|\cdot|_w^{s+it_w}$ if it is odd; and if $a\in\{0,1\}$, $t\in\mathbb R$ satisfy $\chi_w=\mathrm{sgn}^a|\cdot|_w^{it}$, then $a=a_w$ and $t=t_w$;
--   2. if $w$ is complex, there is an integer $n$ with $|n|=|n_w|$ such that for all $x\in F_w^\times$
--   $$\chi_w(x)=\Bigl(\frac{\iota_w(x)}{|\iota_w(x)|}\Bigr)^{n}\,|x|_w^{it_w},$$
--   i.e. $\chi_w|\cdot|_w^s=\chi_{n,s}|\cdot|_w^{it_w}$ with $\chi_{n,s}(re^{i\theta})=e^{in\theta}r^{2s}$; and if $m\in\mathbb Z$, $t\in\mathbb R$ satisfy the same identity, then $m=n$ and $t=t_w$.
--
--   These are the parameters in which the archimedean Euler factors of the completed Hecke $L$-function are written: $\Gamma_{\mathbb R}(s+it_w+a_w)$, where $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$, at a real place and $(2\pi)^{-(s+it_w+|n_w|/2)}\Gamma(s+it_w+|n_w|/2)$ at a complex place (equations (3.2.1.4)–(3.2.1.5), recalled in (6.3.1.4)). The statement says that the parameters attached to $\chi$ by the platform's definition of these factors are the classical ones of Tate's classification of the quasi-characters of $\mathbb R^\times$ and $\mathbb C^\times$.
--
--   **Formalization Note.** $\chi_w$ is `HeckeCharacter.localComponentInfinite`, and $t_w$, $a_w$, $|n_w|$ are `HeckeCharacter.archExponent`, `HeckeCharacter.archParity` and `HeckeCharacter.archWeight` of the platform definition `MasulloGRH_CompletedL` (they are defined by choice, as the parameters whose existence is asserted here). $\iota_w$ is `InfinitePlace.Completion.extensionEmbedding`; at a real place $\mathrm{sgn}(x)^{a}$ is written as $1$ if $\operatorname{Re}\iota_w(x)>0$ and $(-1)^{a}$ otherwise. The hypothesis $a\le1$ in the uniqueness clause only reflects that a parity is $0$ or $1$. **Deviation from the source.** The source (p. 123, before (3.2.1.5)) writes $\chi_{n,s}$ as $(r,\theta)\mapsto r^{s}e^{in\theta}$; since $|\cdot|_w$ is the normalized absolute value ($|z|_w=|z|^2$ at a complex place) and (3.2.1.5) is the Euler factor of $(z/|z|)^n|z|_w^{s}$, the modulus $r=|z|$ enters as $r^{2s}=|z|_w^{s}$, which is the form used here.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 303, §6.3.1 (archimedean case, paragraph before (6.3.1.4)); the parameters enter (3.2.1.4)–(3.2.1.5), p. 123

import Mathlib
import Definitions.Def_MasulloGRH_CompletedL

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem localComponentInfinite_eq_archParameters
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F) :
    (w.IsReal →
      (∀ x : (w.Completion)ˣ,
        χ.localComponentInfinite w x =
          (if 0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re then 1
            else (-1 : ℂ) ^ χ.archParity w) *
          ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((χ.archExponent w : ℂ) * Complex.I)) ∧
      ∀ (a : ℕ) (t : ℝ), a ≤ 1 →
        (∀ x : (w.Completion)ˣ,
          χ.localComponentInfinite w x =
            (if 0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re then 1
              else (-1 : ℂ) ^ a) *
            ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) →
        a = χ.archParity w ∧ t = χ.archExponent w) ∧
    (w.IsComplex →
      ∃ n : ℤ, n.natAbs = χ.archWeight w ∧
        (∀ x : (w.Completion)ˣ,
          χ.localComponentInfinite w x =
            (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
                ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ n *
              ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((χ.archExponent w : ℂ) * Complex.I)) ∧
        ∀ (m : ℤ) (t : ℝ),
          (∀ x : (w.Completion)ˣ,
            χ.localComponentInfinite w x =
              (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
                  ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ m *
                ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) →
          m = n ∧ t = χ.archExponent w) := by sorry

end MasulloGRH
